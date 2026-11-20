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

# Calculation identity excludes documentation, manuscript and the other backend.
# Keep this explicit: see docs/MODULARITY.md for the component contract.
def source_inventory(root: Path) -> dict:
    paths=[root/p for p in ('registry.json','run.py','scripts/driver.py',
                           'scripts/worker.ml','scripts/report_paths.py')]
    for folder in ('ocaml','tests/ocaml'):
        paths.extend((root/folder).glob('*.ml'))
    return {p.relative_to(root).as_posix():digest(p) for p in sorted(set(paths)) if p.is_file()}

def compatibility_record(root: Path) -> dict:
    p=root/'provenance/report-compatibility.json'
    return read_json(p) if p.is_file() else {}

def match_ocaml_sources(source: dict, current: dict, compatibility: dict) -> str | None:
    if source == current:
        return 'CURRENT_COMPONENT'
    # Do not simply discard unknown extra entries in old inventories. Recognize
    # only the exact distributed v004 inventory, then compare EVERY current
    # calculation file. Its original source/environment fingerprint is retained.
    old=compatibility.get('ocaml_v004_source_inventory')
    if source == old and all(source.get(k)==v for k,v in current.items()):
        return 'V004_EXACT_NUMERICAL_COMPONENT'
    return None

def inspect_log(path: Path, job: str) -> bool:
    found=set()
    with path.open(encoding='utf-8',errors='replace') as f:
        for line in f:
            line=line.rstrip('\r\n')
            if line in {STACK_MARKER,'PENTAGON JOB PASS: '+job}:found.add(line)
            if line.startswith(('PENTAGON JOB ERROR:','PENTAGON SETUP ERROR:','Exception:','Fatal error:','TEST FAIL')):
                return False
    return found=={STACK_MARKER,'PENTAGON JOB PASS: '+job}

def inspect_run(folder: Path, current: dict, registry: dict, compatibility: dict | None=None) -> tuple[dict | None,str | None]:
    """Read one controller-produced folder. A malformed folder supplies no passes."""
    try:
        source=read_json(folder/'source-sha256.json')
        source_match=match_ocaml_sources(source,current,compatibility or {})
        if source_match is None: return None,None  # Different calculation; not a pass here.
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
                       'process_exit':row.get('process_exit'),'execution_fingerprint':expected,
                       'source_match':source_match}
        return {'environment':env,'fingerprint':expected,'component_fingerprint':canonical({'source':current,'environment':env}),
                'rows':out,'stamp':folder.name},None
    except (OSError,KeyError,ValueError,TypeError) as ex:
        return None,str(folder)+': '+str(ex)

WOLFRAM_FILES=('PentagonChecks.wl','checks_catalog.json','expected_checks.json')
LEGACY_WOLFRAM_FILES=('PentagonChecks.wl','run_checks.wls','checks_catalog.json','expected_checks.json')

def wolfram_identity(root: Path) -> dict:
    """Local component files only. This function never reads paper/ or OCaml."""
    return {name:digest(root/'mathematica'/name) for name in WOLFRAM_FILES}

def wolfram_source_match(root: Path, report: dict) -> dict:
    current=wolfram_identity(root)
    source=report.get('SourceSHA256')
    if report.get('ReportSchema')==2:
        if report.get('Component')!='PentagonChecks' or report.get('IdentityScope')!='component-local-files':
            raise ValueError('Unrecognized Wolfram component or identity scope')
        if not isinstance(source,dict):raise ValueError('Missing or invalid Wolfram SourceSHA256 object')
        if source != current:
            different=sorted(n for n in set(source)|set(current) if source.get(n)!=current.get(n))
            raise ValueError('Wolfram runtime-file identity differs: '+', '.join(different)+'; no manuscript comparison is made')
        return {'mode':'CURRENT_COMPONENT','source_sha256':source}
    if 'ReportSchema' in report:
        raise ValueError('Unsupported Wolfram report schema')
    # Explicitly audited pre-modular reports, never re-stamped as new executions.
    compat=compatibility_record(root).get('wolfram',{})
    if not isinstance(source,dict) or compat.get('current_source_sha256')!=current:
        raise ValueError('Legacy report not covered by the current checked compatibility record')
    local={name:source.get('mathematica/'+name) for name in LEGACY_WOLFRAM_FILES}
    for entry in compat.get('legacy_reports',[]):
        if local==entry.get('source_sha256'):
            return {'mode':'APPROVED_LEGACY_EQUIVALENCE','source_sha256':source,
                    'equivalence_id':entry['id'],
                    'compatibility_sha256':digest(root/'provenance/report-compatibility.json'),
                    'original_release':report.get('Version'),
                    'original_manuscript':report.get('Manuscript'),
                    'basis':entry['basis']}
    raise ValueError('Legacy Wolfram test-program identity is not recognized')

def inspect_wolfram(root: Path, path: Path) -> dict:
    report=read_json(path)
    if not isinstance(report,dict):raise ValueError('Wolfram report must be a JSON object')
    source_match=wolfram_source_match(root,report)
    expected=read_json(root/'mathematica/expected_checks.json')
    required=expected['required_ids']
    if not required or len(required)!=len(set(required)):
        raise ValueError('Invalid expected Wolfram check set')
    if report.get('SectionsRun')!=expected['sections']:
        raise ValueError('Wolfram confirmation requires every section, in the standard order')
    records=report.get('Checks')
    if not isinstance(records,list) or any(not isinstance(r,dict) for r in records):
        raise ValueError('Wolfram checks must be a list of result objects')
    names=[r.get('ID') for r in records]
    if any(not isinstance(n,str) for n in names) or len(names)!=len(set(names)) or set(names)!=set(required):
        raise ValueError('Wolfram check set is missing, duplicated, or unexpected')
    if (type(report.get('Total')) is not int or report['Total']!=len(required)
        or type(report.get('Failed')) is not int or report['Failed']!=0
        or report.get('AllRequestedChecksPassed') is not True):
        raise ValueError('Wolfram summary is not a complete pass')
    if any(r.get('Passed') is not True for r in records):raise ValueError('Wolfram report contains a failed check')
    return {'status':'PASS','checks':len(required),'report_sha256':digest(path),
            'kernel':report.get('KernelVersion'),'source_match':source_match,
            'source_sha256':report['SourceSHA256'],'report':str(path.resolve())}

def inspect_association(root: Path) -> dict:
    """Check assembly metadata separately; not a numerical-test dependency."""
    p=root/'verification/association.json'
    if not p.is_file():return {'status':'NO_ASSOCIATION','reason':'Missing verification/association.json'}
    try:
        a=read_json(p);files=a['files']
        if a.get('schema')!=1 or not isinstance(files,dict) or not files:
            raise ValueError('Invalid association manifest')
        for name,value in files.items():
            rel=Path(name)
            if rel.is_absolute() or '..' in rel.parts or '\\' in name:
                raise ValueError('Invalid assembly pathname')
            if digest(root/rel)!=value:raise ValueError('Assembly file differs: '+name)
        if digest(root/'mathematica/expected_checks.json')!=a['wolfram_expected_checks_sha256']:
            raise ValueError('Assembly expected-check catalogue differs')
        return {'status':'MATCH','manifest_sha256':digest(p),'manuscript':a['manuscript'],'files':files,
                'scope':'Document association, not mathematical validation of arbitrary manuscript edits.'}
    except (OSError,ValueError,KeyError,TypeError) as ex:
        return {'status':'ASSOCIATION_MISMATCH','reason':str(ex)}

def render_markdown(value: dict) -> str:
    oc=value['ocaml'];wl=value['wolfram']
    lines=['# Verification record — '+value['release'],'',
           'Generated from local execution records. This is not a manually signed assertion or a formal proof certificate.','',
           '**OCaml:** '+oc['status']+f" ({oc['passed']}/{oc['required']} required jobs).",'',
           '**Wolfram supplementary checks:** '+wl['status']+'.','',
           '**Manuscript association:** '+value['association']['status']+'.','',
           '**Combined confirmation:** '+('COMPLETE' if value['complete'] else 'No combined confirmation recorded for these exact sources.')+'.','',
           'OCaml component inventory SHA-256: `'+value['source_inventory_sha256']+'`.','',
           'Revalidate this record after moving or modifying files: `python3 confirm.py --check`.','',
           'The required OCaml set consists of all proof jobs plus unit, extended, contact-sign, and geometric MITM contract tests. Optional diagnostics do not replace proof jobs.','',
           '| Job | Verified status | Seconds |','|---|---|---:|']
    for name,row in oc['jobs'].items():lines.append(f"| `{name}` | {row['status']} | {row.get('wall_seconds','')} |")
    lines+=['', 'Wolfram evidence mode: `'+wl.get('source_match',{}).get('mode','NO_RECORD')+'`.']
    inherited=sum(r.get('source_match')=='V004_EXACT_NUMERICAL_COMPONENT' for r in oc['jobs'].values())
    if inherited:lines+=['',str(inherited)+' OCaml stages retain their original v004 execution fingerprints; their complete numerical component matches this distribution.']
    if wl.get('source_match',{}).get('mode')=='APPROVED_LEGACY_EQUIVALENCE':
        lines+=['','The imported Wolfram JSON is unchanged. Its earlier test program is covered by the explicit mathematical-equivalence record; it is not a new execution of this reporting wrapper.']
    if value['validation_notes']:
        lines+=['','## Record validation notes','']+value['validation_notes']
    lines+=['','## Interpretation','',
      'A completed finite search establishes its encoded exclusion under the documented coordinate and interval contracts. Function tests and symbolic checks have distinct roles. Compiler, library, and source identities accompany the run reports.',
      'Prior timing summaries in evidence/ supply no passes. The only accepted earlier computation records are those covered by the explicit compatibility contract, with intact logs, original fingerprints, and unchanged calculation inputs. No timeout, failure, interruption, or absent log counts as a pass.']
    return '\n'.join(lines)+'\n'

def refresh(root: Path, work: Path | None=None, output: Path | None=None) -> dict:
    root=root.resolve();work=(work or root/'runs').resolve(); output=output or root/'verification'
    current=source_inventory(root);reg=read_json(root/'registry.json');compat=compatibility_record(root)
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
            result,err=inspect_run(folder,current,reg,compat)
            if err:notes.append(err)
            if result:
                group=groups.setdefault(result['component_fingerprint'],{'rows':{},'environment':result['environment'],'stamp':''})
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
    association=inspect_association(root)
    if association['status']!='MATCH':notes.append('Assembly: '+association.get('reason',association['status']))
    value={'schema':2,'identity_scope':'ocaml-calculation-component','release':reg.get('version','unknown'),'generated_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
           'source_inventory_sha256':canonical(current),'source_sha256':current,
           'ocaml':{'status':'COMPLETE' if passed==len(required) else 'NO_COMPLETE_MATCHING_RECORD','passed':passed,'required':len(required),'jobs':jobs,'environment':best['environment']},
           'wolfram':wolfram,'association':association,
           'complete':passed==len(required) and wolfram['status']=='PASS' and association['status']=='MATCH','validation_notes':notes}
    output.mkdir(parents=True,exist_ok=True)
    write_json(output/'status.json',value)
    (output/'CONFIRMATION.md').write_text(render_markdown(value),encoding='utf-8')
    return value

def import_wolfram(root: Path, path: Path) -> dict:
    result=inspect_wolfram(root,path)
    dest=root/'verification/wolfram-report.json';dest.parent.mkdir(parents=True,exist_ok=True)
    if path.resolve()!=dest.resolve():shutil.copyfile(path,dest)
    return result

def prepare_resume(root: Path, work: Path | None=None) -> dict:
    """Rebuild only mutable checkpoints from fully validated current/legacy logs.

    This never changes original run inventories, logs, result rows, or timestamps.
    Original fingerprints and source-match provenance are kept on every cache row.
    """
    work=(work or root/'runs').resolve()
    record=refresh(root,work)
    env=record['ocaml']['environment']
    fp=canonical({'source':source_inventory(root),'environment':env})
    # Include optional diagnostics as well as required jobs. Keep the same
    # selected environment and later-result precedence as refresh().
    registry=read_json(root/'registry.json');compat=compatibility_record(root)
    all_rows={};folders=list(work.iterdir()) if work.is_dir() else []
    archived=root/'verification/run-records'
    if archived.is_dir():folders.extend(archived.iterdir())
    for folder in sorted(folders,key=lambda p:(p.name,str(p))):
        if not folder.is_dir() or not (folder/'results.json').is_file():continue
        result,error=inspect_run(folder,source_inventory(root),registry,compat)
        if result and result['environment']==env:all_rows.update(result['rows'])
    cache={}
    for name,row in all_rows.items():
        if row.get('status')!='PASS':continue
        cache[name]={'id':name,'status':'PASS','process_exit':0,'failure_kind':None,
                     'completion_marker_found':True,'log':row['log'],'log_sha256':row['log_sha256'],
                     'wall_seconds':row.get('wall_seconds',0),'fingerprint':fp,
                     'original_execution_fingerprint':row['execution_fingerprint'],
                     'cache_basis':row['source_match']}
    work.mkdir(parents=True,exist_ok=True)
    p=work/'checkpoints.json'
    if p.is_file():
        backup=work/('checkpoints.before-modular-'+dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'.json')
        shutil.copyfile(p,backup)
    write_json(p,cache)
    return {'prepared':len(cache),'checkpoint':str(p)}

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
            if (rel.parts[0]=='runs' and rel.as_posix()!='runs/README.md') or rel.parts[:2]==('verification','run-records'):continue
            if p.is_symlink():raise ValueError('Refusing to package a symlink: '+str(rel))
            if p.suffix in {'.aux','.log','.toc','.out','.synctex.gz'} and rel.parts[0] not in {'evidence','verification'}:continue
            z.write(p,prefix+str(rel))
        for folder in sorted(reports):
            for p in sorted(folder.rglob('*')):
                if p.is_file():z.write(p,prefix+'verification/run-records/'+folder.name+'/'+str(p.relative_to(folder)))
    return destination
