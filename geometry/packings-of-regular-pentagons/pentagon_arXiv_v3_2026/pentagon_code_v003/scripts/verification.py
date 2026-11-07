"""Build a source-specific verification record from checked local execution logs.

This module never executes a mathematical calculation and never treats a saved
status word as sufficient evidence. It checks the report's source inventory,
execution fingerprint, exit status, completion markers, and each log digest.
The record is an execution summary, not a formal proof certificate.
"""
from __future__ import annotations
import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil
import zipfile

SUCCESS = {"PASS", "CACHED_PASS"}
STACK_MARKER = "PENTAGON STACK RETAINED: 16777216"

def digest(p: Path) -> str:
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024**2),b''):h.update(block)
    return h.hexdigest()

def canonical(x) -> str:
    return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def read_json(p: Path):
    return json.loads(p.read_text(encoding='utf-8'))

def write_json(p: Path, value):
    p.parent.mkdir(parents=True,exist_ok=True)
    tmp=p.with_name(p.name+'.tmp')
    tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    tmp.replace(p)

def source_inventory(root: Path) -> dict:
    paths=[root/'registry.json',root/'run.py',root/'confirm.py',root/'RELEASE.json']
    for rel in ['paper/pentagon_v005.tex','paper/label-map.json']:
        if (root/rel).is_file(): paths.append(root/rel)
    for folder in ['ocaml','scripts','tests/ocaml','mathematica']:
        paths.extend(p for p in (root/folder).rglob('*') if p.is_file() and p.suffix in {'.ml','.py','.json','.wl','.wls'})
    # Relative identities survive moving the complete distribution to another folder.
    return {str(p.relative_to(root)):digest(p) for p in sorted(set(paths)) if p.is_file()}

def inspect_log(path: Path, job: str) -> bool:
    found=set()
    with path.open(encoding='utf-8',errors='replace') as f:
        for line in f:
            line=line.rstrip('\r\n')
            if line in {STACK_MARKER,'PENTAGON JOB PASS: '+job}:found.add(line)
            if line.startswith(('PENTAGON JOB ERROR:','PENTAGON SETUP ERROR:','Exception:','Fatal error:','TEST FAIL')):
                return False
    return found=={STACK_MARKER,'PENTAGON JOB PASS: '+job}

def inspect_run(folder: Path, current: dict, registry: dict) -> tuple[dict | None,str | None]:
    """Read one controller-produced folder. A malformed folder supplies no passes."""
    try:
        source=read_json(folder/'source-sha256.json')
        if source!=current: return None,None  # Different release; not an error or a pass here.
        env=read_json(folder/'environment/environment.json')
        expected=canonical({'source':source,'environment':env})
        if read_json(folder/'fingerprint.json').get('value')!=expected:
            raise ValueError('environment/source fingerprint mismatch')
        selected=read_json(folder/'plan.json')['jobs']
        ids=[j['id'] for j in selected]
        known={j['id'] for j in registry['jobs']}
        if len(ids)!=len(set(ids)) or not set(ids)<=known:raise ValueError('invalid selected job set')
        rows=read_json(folder/'results.json')
        if not isinstance(rows,list):raise ValueError('results are not a list')
        seen=set();out={}
        for row in rows:
            name=row.get('id')
            if name not in ids or name in seen:raise ValueError('duplicate or unselected result')
            seen.add(name)
            p=folder/(name+'.log')
            passed=(row.get('status') in SUCCESS and row.get('process_exit')==0 and
                    row.get('fingerprint')==expected and row.get('failure_kind') is None and
                    p.is_file() and digest(p)==row.get('log_sha256') and inspect_log(p,name))
            if row.get('status') in SUCCESS and not passed:
                raise ValueError('invalid successful result: '+name)
            out[name]={'status':'PASS' if passed else row.get('status','NOT_RUN'),
                       'report_folder':str(folder.resolve()),'log':str(p.resolve()) if p.is_file() else None,
                       'log_sha256':row.get('log_sha256'),'wall_seconds':row.get('wall_seconds'),
                       'process_exit':row.get('process_exit'),'execution_fingerprint':expected}
        return {'environment':env,'fingerprint':expected,'rows':out,'stamp':folder.name},None
    except (OSError,KeyError,ValueError,TypeError) as ex:
        return None,str(folder)+': '+str(ex)

def wolfram_identity(root: Path) -> dict:
    rels=['mathematica/PentagonChecks.wl','mathematica/run_checks.wls','mathematica/checks_catalog.json',
          'mathematica/expected_checks.json','paper/pentagon_v005.tex','paper/label-map.json']
    return {rel:digest(root/rel) for rel in rels}

def inspect_wolfram(root: Path, path: Path) -> dict:
    report=read_json(path)
    expected=read_json(root/'mathematica/expected_checks.json')
    required=set(expected['required_ids'])
    if report.get('SourceSHA256')!=wolfram_identity(root):raise ValueError('Wolfram source/manuscript identity differs')
    if report.get('SectionsRun')!=expected['sections']:raise ValueError('Wolfram confirmation requires every section, in the standard order')
    records=report.get('Checks',[])
    names=[r.get('ID') for r in records]
    if len(names)!=len(set(names)) or set(names)!=required:raise ValueError('Wolfram check set is missing, duplicated, or unexpected')
    if report.get('Total')!=len(required) or report.get('Failed')!=0 or report.get('AllRequestedChecksPassed') is not True:
        raise ValueError('Wolfram summary is not a complete pass')
    if any(r.get('Passed') is not True for r in records):raise ValueError('Wolfram report contains a failed check')
    return {'status':'PASS','checks':len(required),'report_sha256':digest(path),'kernel':report.get('KernelVersion'),
            'source_sha256':report['SourceSHA256'],'report':str(path.resolve())}

def render_markdown(value: dict) -> str:
    oc=value['ocaml'];wl=value['wolfram']
    lines=['# Verification record — '+value['release'],'',
           'Generated from local execution records. This is not a manually signed assertion or a formal proof certificate.','',
           '**OCaml:** '+oc['status']+f" ({oc['passed']}/{oc['required']} required jobs).",'',
           '**Wolfram supplementary checks:** '+wl['status']+'.','',
           '**Combined confirmation:** '+('COMPLETE' if value['complete'] else 'No combined confirmation recorded for these exact sources.')+'.','',
           'Source inventory SHA-256: `'+value['source_inventory_sha256']+'`.','',
           'Revalidate this record after moving or modifying files: `python3 confirm.py --check`.','',
           'The required OCaml set consists of all proof jobs plus unit, extended, and contact-sign contract tests. Optional diagnostics do not replace proof jobs.','',
           '| Job | Verified status | Seconds |','|---|---|---:|']
    for name,row in oc['jobs'].items():lines.append(f"| `{name}` | {row['status']} | {row.get('wall_seconds','')} |")
    if value['validation_notes']:
        lines+=['','## Record validation notes','']+value['validation_notes']
    lines+=['','## Interpretation','',
      'A completed finite search establishes its encoded exclusion under the documented coordinate and interval contracts. Function tests and symbolic checks have distinct roles. Compiler, library, and source identities accompany the run reports.',
      'Prior-version evidence in evidence/ is not used to fill current-release missing jobs. No timeout, failure, interrupted run, or absent log counts as a pass.']
    return '\n'.join(lines)+'\n'

def refresh(root: Path, work: Path | None=None, output: Path | None=None) -> dict:
    root=root.resolve();work=(work or root/'runs').resolve(); output=output or root/'verification'
    current=source_inventory(root);reg=read_json(root/'registry.json')
    required=[j['id'] for j in reg['jobs'] if j.get('required_for_confirmation',j['role']=='proof')]
    if not required or len(required)!=len(set(required)):raise ValueError('Invalid required verification set')
    groups={};notes=[]
    folders=[]
    if work.is_dir():folders.extend(work.iterdir())
    archived=root/'verification/run-records'
    if archived.is_dir():folders.extend(archived.iterdir())
    if folders:
        for folder in sorted(folders,key=lambda p:(p.name,str(p))):
            if not folder.is_dir() or not (folder/'results.json').is_file():continue
            result,err=inspect_run(folder,current,reg)
            if err:notes.append(err)
            if result:
                group=groups.setdefault(result['fingerprint'],{'rows':{},'environment':result['environment'],'stamp':''})
                group['rows'].update(result['rows']);group['stamp']=result['stamp']
    # Do not merge executions made with different runtime/library fingerprints.
    best=max(groups.values(),key=lambda g:(sum(g['rows'].get(n,{}).get('status')=='PASS'for n in required),g['stamp']),default={'rows':{},'environment':{},'stamp':''})
    jobs={n:best['rows'].get(n,{'status':'NO_MATCHING_RUN'}) for n in required}
    passed=sum(row['status']=='PASS' for row in jobs.values())
    wolfram={'status':'NO_MATCHING_RECORD'}
    wf=root/'verification/wolfram-report.json'
    if wf.is_file():
        try:wolfram=inspect_wolfram(root,wf)
        except (OSError,ValueError,KeyError,TypeError) as ex:
            wolfram={'status':'RECORD_MISMATCH','reason':str(ex)};notes.append('Wolfram: '+str(ex))
    value={'schema':1,'release':reg.get('version','unknown'),'generated_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
           'source_inventory_sha256':canonical(current),'source_sha256':current,
           'ocaml':{'status':'COMPLETE' if passed==len(required) else 'NO_COMPLETE_MATCHING_RECORD','passed':passed,'required':len(required),'jobs':jobs,'environment':best['environment']},
           'wolfram':wolfram,'complete':passed==len(required) and wolfram['status']=='PASS','validation_notes':notes}
    output.mkdir(parents=True,exist_ok=True)
    write_json(output/'status.json',value)
    (output/'CONFIRMATION.md').write_text(render_markdown(value),encoding='utf-8')
    return value

def import_wolfram(root: Path, path: Path) -> dict:
    result=inspect_wolfram(root,path)
    dest=root/'verification/wolfram-report.json';dest.parent.mkdir(parents=True,exist_ok=True)
    if path.resolve()!=dest.resolve():shutil.copyfile(path,dest)
    return result

def make_bundle(root: Path, destination: Path, record: dict) -> Path:
    if not record.get('complete'):raise ValueError('The source-matching OCaml and Wolfram records are required for a verified bundle')
    destination=destination.expanduser().resolve()
    if destination.exists():raise FileExistsError('Refusing to overwrite '+str(destination))
    # Include one copy of each contributing report directory, not every old failed run.
    reports={Path(r['report_folder']).resolve() for r in record['ocaml']['jobs'].values()}
    destination.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(destination,'x',zipfile.ZIP_DEFLATED) as z:
        prefix=root.name+'/'
        for p in sorted(root.rglob('*')):
            if not p.is_file() or p.resolve()==destination:continue
            rel=p.relative_to(root)
            if any(x in {'.git','__pycache__','.pytest_cache'} for x in rel.parts):continue
            if rel.parts[0]=='runs' or rel.parts[:2]==('verification','run-records'):continue
            if p.is_symlink():raise ValueError('Refusing to package a symlink: '+str(rel))
            if p.suffix in {'.aux','.log','.toc','.out','.synctex.gz'} and rel.parts[0] not in {'evidence','verification'}:continue
            z.write(p,prefix+str(rel))
        for folder in sorted(reports):
            for p in sorted(folder.rglob('*')):
                if p.is_file():z.write(p,prefix+'verification/run-records/'+folder.name+'/'+str(p.relative_to(folder)))
    return destination
