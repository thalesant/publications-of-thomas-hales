"""Resource-bounded, resumable execution of explicitly selected OCaml jobs.

Only orchestration lives here. No numerical formula is evaluated by this driver.
A PASS requires a normal process exit, the job marker and retained stack marker.
Changing a source, adapter, installed-library fingerprint or this driver invalidates
current-release checkpoints. Historical reports are never imported as new passes.
"""
from __future__ import annotations
import argparse, datetime as dt, fcntl, hashlib, json, math, os
from pathlib import Path
import platform, resource, shutil, signal, subprocess, sys, time, traceback, uuid, zipfile

ROOT = Path(__file__).resolve().parents[1]
VERSION = "pentagon_code_v003"
STACK_MARKER = "PENTAGON STACK RETAINED: 16777216"
LOG_CAP = 64 * 1024**2
GIB = 1024**3
SUCCESS = {"PASS", "CACHED_PASS"}

def digest(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda: f.read(1024**2), b""): h.update(b)
    return h.hexdigest()

def canonical(x) -> str:
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def write_json(p: Path, x) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    q = p.with_name(p.name + ".tmp")
    q.write_text(json.dumps(x, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    q.replace(p)

def source_inventory(root: Path) -> dict:
    from scripts.verification import source_inventory as inventory
    return inventory(root)

def select_jobs(registry: dict, args) -> list[dict]:
    jobs = registry["jobs"]
    by_id = {j["id"]: j for j in jobs}
    if len(by_id) != len(jobs): raise ValueError("Duplicate job identifiers")
    selected = set()
    for name in args.job or []:
        if name not in by_id: raise ValueError("Unknown job: " + name)
        selected.add(name)
    for claim in args.claim or []:
        matches = [j["id"] for j in jobs if claim in j.get("claims", []) or claim in j.get("aliases", [])]
        if not matches: raise ValueError("Unknown or job-free claim: " + claim + "; consult docs/CALCULATIONS.md")
        selected.update(matches)
    for section in args.section or []:
        matches = [j["id"] for j in jobs if section in j.get("sections", [])]
        if not matches: raise ValueError("Unknown section: " + section)
        selected.update(matches)
    if args.all:
        selected.update(j["id"] for j in jobs if j["role"] == "proof")
    if args.changed:
        selected.update(j["id"] for j in jobs if j.get("changed_domain") or j.get("changed_contract"))
    if args.diagnostics:
        selected.update(j["id"] for j in jobs if j["role"] == "diagnostic")
    # A default invocation is a small function-contract check, not a proof search.
    if args.tests or not selected:
        selected.add("unit")
        if "squeeze_sign_tests" in by_id: selected.add("squeeze_sign_tests")
    if args.extended or args.all or args.changed:
        selected.add("extended")
    if any(by_id[i]["role"] != "test" for i in selected): selected.add("unit")
    if args.all or any(i.startswith("squeeze_sign_") for i in selected):
        if "squeeze_sign_tests" in by_id: selected.add("squeeze_sign_tests")
    missing=selected-set(by_id)
    if missing: raise ValueError("Registry is missing required test jobs: " + ", ".join(sorted(missing)))
    test_prerequisites=[i for i in ["unit","extended","squeeze_sign_tests"] if i in selected]
    result = []
    for j in jobs:
        if j["id"] in selected:
            j = dict(j)
            if j["id"] == "unit": j["deps"] = []
            elif j["role"] == "test": j["deps"] = ["unit"]
            else: j["deps"] = list(test_prerequisites)
            result.append(j)
    if not result: raise ValueError("Empty selection is not a successful run")
    return result

def memory_info() -> dict:
    out = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        k, _, v = line.partition(":")
        if k in {"MemTotal", "MemAvailable", "SwapTotal", "SwapFree"}: out[k] = int(v.split()[0])*1024
    if "MemAvailable" not in out: raise RuntimeError("Cannot determine available memory")
    total, avail = out["MemTotal"], out["MemAvailable"]
    groups = [Path("/sys/fs/cgroup")]
    try:
        for line in Path("/proc/self/cgroup").read_text().splitlines():
            if line.startswith("0::"):
                p = Path("/sys/fs/cgroup")/line[3:].lstrip("/")
                groups += [p] + list(p.parents)
    except OSError: pass
    for p in set(groups):
        if not p.is_relative_to(Path("/sys/fs/cgroup")): continue
        try:
            s = (p/"memory.max").read_text().strip()
            if s != "max":
                cap=int(s); used=int((p/"memory.current").read_text())
                total=min(total,cap); avail=min(avail,max(0,cap-used))
        except (OSError,ValueError): pass
    out.update(effective_total=total,effective_available=avail)
    return out

def rss(pid: int) -> int:
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"): return int(line.split()[1])*1024
    except (OSError,ValueError): pass
    return 0

def admission_ok(available: int, reserve: int, cap: int, current: list[int]) -> bool:
    return available >= reserve + cap + sum(max(0,cap-min(cap,max(0,x))) for x in current)

def scan_completion(log: Path, ident: str) -> tuple[bool, str | None]:
    marker="PENTAGON JOB PASS: "+ident
    found=set();failure=None
    for line in log.read_text(encoding="utf-8",errors="replace").splitlines():
        if line in {marker, STACK_MARKER}: found.add(line)
        if line.startswith(("PENTAGON JOB ERROR:","PENTAGON SETUP ERROR:","Exception:","Fatal error:")):
            failure = "UNEXPECTED_EXCEPTION"
            for needle,label in [("Stack overflow","STACK_OVERFLOW"),("Stack_overflow","STACK_OVERFLOW"),("Out_of_memory","OUT_OF_MEMORY"),("Out of memory","OUT_OF_MEMORY"),("Domain_error","DOMAIN_ERROR")]:
                if needle in line: failure=label
        if line.startswith("TEST FAIL"): failure="TEST_FAILURE"
    return {marker,STACK_MARKER}.issubset(found),failure

def cache_valid(row: dict, ident: str, fp: str) -> bool:
    if row.get("status") not in SUCCESS or row.get("fingerprint") != fp or row.get("process_exit") != 0: return False
    p=Path(row.get("log",""))
    try:
        if not p.is_file() or digest(p) != row.get("log_sha256"): return False
        ok, failure=scan_completion(p,ident)
        return ok and failure is None
    except OSError: return False

class StopControl:
    def __init__(self): self.drain=False; self.cancel=False; self.requests=0
    def handle(self, signum, frame):
        self.requests+=1; self.drain=True
        if signum==signal.SIGTERM or self.requests>=2: self.cancel=True

class Running:
    def __init__(self, job, command, cwd, log, env, timeout, cap):
        self.job=job;self.log=log;self.started=time.monotonic();self.timeout=timeout
        self.stop_reason=None;self.stop_started=None;self.usage=None;self.sampled_peak=0
        self.file=log.open("wb")
        self.file.write(("COMMAND "+json.dumps(command)+"\n").encode());self.file.flush()
        def limits():
            signal.signal(signal.SIGINT,signal.SIG_DFL);signal.signal(signal.SIGTERM,signal.SIG_DFL)
            resource.setrlimit(resource.RLIMIT_CORE,(0,0))
            for typ,bound in [(resource.RLIMIT_AS,cap),(resource.RLIMIT_FSIZE,LOG_CAP)]:
                soft,hard=resource.getrlimit(typ)
                if hard != resource.RLIM_INFINITY: bound=min(bound,hard)
                if soft != resource.RLIM_INFINITY: bound=min(bound,soft)
                resource.setrlimit(typ,(bound,bound))
        try:
            # The controller is single threaded. No thread-pool preexec_fn hazard.
            self.proc=subprocess.Popen(command,cwd=cwd,env=env,stdin=subprocess.DEVNULL,stdout=self.file,
                stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
        except BaseException: self.file.close();raise
    def stop(self, reason):
        if self.stop_started is not None:return
        self.stop_reason=reason;self.stop_started=time.monotonic()
        try:os.killpg(self.proc.pid,signal.SIGTERM)
        except ProcessLookupError:pass
    def poll(self):
        self.sampled_peak=max(self.sampled_peak,rss(self.proc.pid))
        pid,status,usage=os.wait4(self.proc.pid,os.WNOHANG)
        if pid:
            self.proc.returncode=os.waitstatus_to_exitcode(status);self.usage=usage;return True
        if self.timeout and time.monotonic()-self.started>=self.timeout:self.stop("TIMEOUT")
        if self.stop_started is not None and time.monotonic()-self.stop_started>10:
            try:os.killpg(self.proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
        return False
    def finish(self):
        code=self.proc.returncode;elapsed=time.monotonic()-self.started
        self.file.write(f"\nPROCESS EXIT: {code}\nWALL SECONDS: {elapsed:.3f}\n".encode());self.file.close()
        ok,failure=scan_completion(self.log,self.job["id"])
        if code==-signal.SIGXFSZ:failure="LOG_LIMIT"
        if code==-signal.SIGKILL and self.stop_reason is None:failure="KILLED_UNCLASSIFIED"
        status=self.stop_reason or ("PASS" if code==0 and ok and failure is None else "FAILED")
        return dict(status=status,process_exit=code,completion_marker_found=ok,failure_kind=failure,
          wall_seconds=round(elapsed,3),peak_rss_bytes=int(self.usage.ru_maxrss)*1024,
          cpu_user_seconds=self.usage.ru_utime,cpu_system_seconds=self.usage.ru_stime,
          log=str(self.log),log_sha256=digest(self.log))

def environment(switch: str, folder: Path, root: Path):
    opam=shutil.which("opam")
    if not opam:raise RuntimeError("opam was not found. See docs/INSTALL.md; no installation was attempted.")
    prefix=[opam,"exec","--switch="+switch,"--set-switch","--"]
    env=dict(os.environ);env.update(OPAMCOLOR="never",PENTAGON_ROOT=str(root))
    commands={"compiler":prefix+["ocamlc","-config"],"packages":[opam,"list","--switch="+switch,"--installed","--columns=name,version"],
      "pins":[opam,"pin","list","--switch="+switch],"prefix":[opam,"var","--switch="+switch,"prefix"]}
    folder.mkdir(parents=True,exist_ok=True);details={}
    for name,cmd in commands.items():
        p=subprocess.run(cmd,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
        text=p.stdout.decode(errors="replace");(folder/(name+".txt")).write_text(text+p.stderr.decode(errors="replace"))
        if p.returncode:raise RuntimeError("Environment command failed: "+name)
        details[name]=text.strip()
    if "version: 4.14.4" not in details["compiler"]:raise RuntimeError("Use OCaml 4.14.4 for this release; other compilers need separate validation.")
    installed=Path(details["prefix"])
    if not installed.is_absolute() or not (installed/"lib").is_dir():raise RuntimeError("Invalid opam switch prefix")
    fingerprints={}
    for p in sorted((installed/"lib").rglob("*")):
        if p.is_file():fingerprints[str(p.relative_to(installed))]=digest(p)
    for name in ["ocaml","ocamlrun","ocamlc","ocamlfind"]:
        p=installed/"bin"/name
        if p.is_file():fingerprints["bin/"+name]=digest(p)
    write_json(folder/"installed-sha256.json",fingerprints)
    details["installed_fingerprint"]=canonical(fingerprints)
    details["platform"]=platform.platform();details["machine"]=platform.machine()
    details["floating_environment"]={k:env.get(k) for k in ["OCAMLRUNPARAM","OCAMLPARAM","OCAMLPATH","OCAML_TOPLEVEL_PATH","LD_PRELOAD","LD_LIBRARY_PATH"]}
    # Export the environment actually selected; never substitute a dependency while running.
    r=subprocess.run([opam,"switch","export","--switch="+switch,"--full",str(folder/"switch.opam")],
      env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
    (folder/"export.log").write_bytes(r.stdout)
    if r.returncode:raise RuntimeError("Switch export failed")
    write_json(folder/"environment.json",details)
    return details,prefix,env

def summary(rows,plan,error):
    out=["# Pentagon code v003 — execution report","","Results concern these exact sources and environment, not every mathematical contract.","",
      "| Job | Status | Seconds | Peak GiB |","|---|---|---:|---:|"]
    by={r["id"]:r for r in rows}
    for j in plan:
        r=by.get(j["id"],{});peak=r.get("peak_rss_bytes")
        out.append(f"| `{j['id']}` | {r.get('status','NOT_RUN')} | {r.get('wall_seconds','')} | {peak/GIB if peak is not None else ''} |")
    if error:out.extend(["","## Controller note",str(error)])
    out.extend(["","A timeout, width limit, exception or interruption is not a counterexample and is not a pass.",
      "A cached pass retains its original log and run identity. Prior-source executions do not fill missing current-release jobs."])
    return "\n".join(out)+"\n"

def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--job",action="append");ap.add_argument("--claim",action="append");ap.add_argument("--section",action="append")
    ap.add_argument("--all",action="store_true");ap.add_argument("--changed",action="store_true")
    ap.add_argument("--tests",action="store_true");ap.add_argument("--extended",action="store_true")
    ap.add_argument("--diagnostics",action="store_true");ap.add_argument("--list",action="store_true")
    ap.add_argument("--switch",default="pentagon-4.14.4");ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--memory-gib",type=float,default=4);ap.add_argument("--reserve-gib",type=float,default=8)
    ap.add_argument("--timeout",type=int,default=259200);ap.add_argument("--rerun",action="store_true")
    ap.add_argument("--work",type=Path,default=ROOT/"runs")
    ap.add_argument("--copy-report",type=Path,help="Copy the report to this directory, or use windows-downloads for WSL known-folder discovery")
    args=ap.parse_args(argv)
    if args.jobs<1 or not math.isfinite(args.memory_gib) or args.memory_gib<.25 or not math.isfinite(args.reserve_gib) or args.reserve_gib<0 or args.timeout<0:ap.error("Invalid resource limits")
    registry=json.loads((ROOT/"registry.json").read_text())
    try:plan=select_jobs(registry,args)
    except ValueError as e:ap.error(str(e))
    if args.list:
        for j in plan:print(f"{j['id']:42} {j['role']:10} {', '.join(j.get('display_claims',j['claims']))}")
        return 0
    if sys.platform!="linux":ap.error("Run in Linux/Ubuntu/WSL, not Windows Python. See docs/INSTALL.md.")
    work=args.work.expanduser().resolve()
    protected=[ROOT]+[ROOT/x for x in ["ocaml","scripts","tests","paper","docs","environment","evidence","mathematica","figures","provenance","licenses","verification"]]
    if work==ROOT or any(work==p or work.is_relative_to(p) for p in protected[1:]):
        ap.error("The output directory must be outside source/document directories; use the default runs directory.")
    work.mkdir(parents=True,exist_ok=True)
    lock=(work/"run.lock").open("a+")
    try:fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:print("Another runner owns this output directory; no job started.");return 2
    stamp=dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")+"-"+uuid.uuid4().hex[:6]
    run=work/stamp;run.mkdir();rows=[];error=None;active={};control=StopControl()
    old_handlers={s:signal.signal(s,control.handle) for s in [signal.SIGINT,signal.SIGTERM]}
    cachepath=work/"checkpoints.json";cache={};source={}
    try:
        write_json(run/"plan.json",dict(version=VERSION,jobs=plan,resources=vars(args)|{"work":str(work),"copy_report":str(args.copy_report) if args.copy_report else None}))
        print(f"Pentagon code v003: {len(plan)} selected jobs; at most {args.jobs} workers.",flush=True)
        print("First Ctrl+C drains active jobs; second cancels. Sources are read-only.",flush=True)
        print("Report directory: "+str(run),flush=True)
        source=source_inventory(ROOT);write_json(run/"source-sha256.json",source)
        for rel in source:
            dest=run/"source"/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,dest)
        details,prefix,env=environment(args.switch,run/"environment",ROOT)
        fp=canonical(dict(source=source,environment=details));write_json(run/"fingerprint.json",{"value":fp})
        if cachepath.exists():cache=json.loads(cachepath.read_text())
        source_changed=False
        pending=list(plan);finished={};cap=int(args.memory_gib*GIB);reserve=int(args.reserve_gib*GIB)
        info=memory_info()
        if info['effective_total']<cap+reserve:
            raise RuntimeError("Memory budget exceeds visible RAM. Reduce --jobs/--reserve-gib or adjust WSL allocation; no job started.")
        heartbeat=time.monotonic();memory_wait=None
        while pending or active:
            if source_inventory(ROOT)!=source:
                error="Source changed while jobs were running";source_changed=True;control.cancel=True;control.drain=True
            if control.cancel:
                for r in active.values():r.stop("INTERRUPTED")
            for ident,r in list(active.items()):
                if r.poll():
                    row=dict(id=ident,**r.finish(),fingerprint=fp)
                    if source_changed:row["status"]="SOURCE_CHANGED"
                    rows.append(row);finished[ident]=row["status"]
                    print(f"{row['status']:12} {ident} ({row['wall_seconds']:.1f}s)",flush=True)
                    if row['status']=='PASS':
                        cache[ident]=row
                    else:
                        cache.pop(ident,None)
                    write_json(cachepath,cache)
                    if row.get('failure_kind') in {'STACK_OVERFLOW','OUT_OF_MEMORY','LOG_LIMIT','KILLED_UNCLASSIFIED'}:
                        control.drain=True;error="Resource failure: "+ident+". Remaining active jobs may finish."
                    del active[ident];write_json(run/"results.json",rows)
            if not control.drain:
                for j in list(pending):
                    ident=j['id'];deps=j['deps']
                    if any(d in finished and finished[d] not in SUCCESS for d in deps):
                        rows.append(dict(id=ident,status="BLOCKED",dependencies=deps));finished[ident]="BLOCKED";pending.remove(j);continue
                    if any(d not in finished for d in deps):continue
                    prior=cache.get(ident,{})
                    if not args.rerun and cache_valid(prior,ident,fp):
                        dest=run/(ident+".log");shutil.copyfile(prior['log'],dest)
                        row=dict(prior,id=ident,status="CACHED_PASS",cached_from=prior['log'],log=str(dest));rows.append(row);finished[ident]="CACHED_PASS";pending.remove(j)
                        print("CACHED_PASS  "+ident,flush=True);continue
                    if len(active)>=args.jobs:break
                    info=memory_info()
                    if not admission_ok(info['effective_available'],reserve,cap,[rss(r.proc.pid) for r in active.values()]):break
                    jobenv=dict(env,PENTAGON_JOB=ident, PENTAGON_DESCRIPTION=j.get("description",ident),
                                PENTAGON_CLAIMS="; ".join(j.get("display_claims",[])),
                                PENTAGON_COMMENT_CODES=", ".join(j.get("comment_ids",[])))
                    command=prefix+["ocaml","-noinit","-I",str(ROOT/"ocaml"),str(ROOT/"scripts/worker.ml")]
                    active[ident]=Running(j,command,ROOT,run/(ident+".log"),jobenv,args.timeout,cap)
                    pending.remove(j);print(f"RUN          {ident} ({len(active)}/{args.jobs} workers)",flush=True)
            if control.drain and not active:break
            if pending and not active and not control.drain:
                # Do not wait forever when other programs leave no admission headroom.
                if memory_wait is None:memory_wait=time.monotonic()
                if time.monotonic()-memory_wait>60:
                    error="Insufficient current memory headroom; pending jobs not run. Retry later or reduce the reserve explicitly.";break
            else:memory_wait=None
            if time.monotonic()-heartbeat>=60:
                sample=memory_info();write_json(run/"memory-last.json",sample)
                print(f"ACTIVE {len(active)}; pending {len(pending)}; available {sample['effective_available']/GIB:.2f} GiB" + ("; DRAINING" if control.drain else ""),flush=True)
                heartbeat=time.monotonic()
            write_json(run/"results.json",rows)
            if pending or active:time.sleep(.25)
        for j in pending:rows.append(dict(id=j['id'],status="NOT_RUN"))
        if control.drain and error is None:error="Stopped after requested drain; completed results retained."
    except Exception as ex:
        error=str(ex);(run/"controller-error.txt").write_text(traceback.format_exc())
        print("CONTROLLER ERROR: "+error,flush=True)
    finally:
        for r in active.values():r.stop("CONTROLLER_STOP")
        for ident,r in list(active.items()):
            while not r.poll():time.sleep(.1)
            rows.append(dict(id=ident,**r.finish()))
        write_json(run/"results.json",rows);write_json(run/"final.json",dict(error=error,interrupted=control.drain))
        (run/"SUMMARY.md").write_text(summary(rows,plan,error))
        # Keep publication prose independent of run status. The generated record
        # is recomputed from exact source identities, exit codes and intact logs.
        try:
            from scripts.verification import refresh
            record=refresh(ROOT,work)
            shutil.copyfile(ROOT/"verification/status.json",run/"verification-status.json")
            shutil.copyfile(ROOT/"verification/CONFIRMATION.md",run/"CONFIRMATION.md")
            print("OCaml confirmation: %d/%d required jobs." %
                  (record['ocaml']['passed'],record['ocaml']['required']),flush=True)
        except Exception as ex:
            (run/"confirmation-error.txt").write_text(str(ex))
            print("Confirmation could not be updated: "+str(ex),flush=True)
            if error is None:error="Confirmation record error: "+str(ex)
        write_json(run/"final.json",dict(error=error,interrupted=control.drain))
        (run/"SUMMARY.md").write_text(summary(rows,plan,error))
        archive=work/("pentagon_code_v003_report_"+stamp+".zip")
        with zipfile.ZipFile(archive,"w",zipfile.ZIP_DEFLATED) as z:
            for p in sorted(run.rglob('*')):
                if p.is_file():z.write(p,str(p.relative_to(run)))
        if args.copy_report:
            try:
                from scripts.report_paths import report_destination
                target=report_destination(args.copy_report);target.mkdir(parents=True,exist_ok=True)
                dest=target/archive.name
                with archive.open('rb') as a,dest.open('xb') as b:shutil.copyfileobj(a,b)
                archive=dest
            except (OSError,ValueError,subprocess.SubprocessError) as ex:
                print("Report copy was not made; original ZIP is retained: "+str(ex),flush=True)
        print("One report ZIP: "+str(archive),flush=True)
        for s,h in old_handlers.items():signal.signal(s,h)
        fcntl.flock(lock.fileno(),fcntl.LOCK_UN);lock.close()
    return 0 if error is None and len(rows)==len(plan) and all(r['status'] in SUCCESS for r in rows) else 1
