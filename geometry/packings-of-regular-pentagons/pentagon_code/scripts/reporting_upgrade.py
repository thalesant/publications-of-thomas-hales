"""Guarded application of the reporting-only v004 update (Linux/WSL).

The caller supplies exact old/new hashes and bytes. No mathematical computation
is executed, and no historical run result, original log, or Wolfram JSON is edited.
"""
from __future__ import annotations
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import tempfile
import uuid
import zipfile


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_path(root: Path, name: str) -> Path:
    p=PurePosixPath(name)
    if p.is_absolute() or '\\' in name or any(x in {'','.','..'} for x in name.split('/')):
        raise ValueError('Invalid update path: '+name)
    target=root.joinpath(*p.parts)
    for parent in [target]+list(target.parents):
        if parent==root:break
        if parent.is_symlink():raise ValueError('Refusing a symlink path: '+name)
    return target


def apply_update(root: Path, files: dict[str, bytes], old_hashes: dict[str, str | None],
                 protected_hashes: dict[str,str], work: Path | None=None) -> dict:
    root=root.expanduser().resolve()
    if not (root/'run.py').is_file() or not (root/'registry.json').is_file():
        raise ValueError('--root must name the existing project directory containing run.py and registry.json')
    if set(files)!=set(old_hashes):raise ValueError('Incomplete update payload')
    for name,sha in protected_hashes.items():
        p=safe_path(root,name)
        if not p.is_file() or digest_bytes(p.read_bytes())!=sha:
            raise ValueError('A numerical/runtime prerequisite differs; nothing changed: '+name)
    work=(work or root/'runs').expanduser().resolve()
    work.mkdir(parents=True,exist_ok=True)
    with (work/'run.lock').open('a+') as lock:
        try:fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('An OCaml runner is active. Let it finish; no source has been changed. The standalone Mathematica folder can be used independently now.')
        changed={}; originals={}
        for name,data in files.items():
            p=safe_path(root,name)
            if p.exists() and not p.is_file():raise ValueError('Expected a regular file: '+name)
            before=p.read_bytes() if p.exists() else None
            if before==data:continue
            actual=digest_bytes(before) if before is not None else None
            if actual!=old_hashes[name]:
                raise ValueError('Unrecognized or locally edited file; nothing changed: '+name)
            changed[name]=data;originals[name]=before
        if not changed:return {'status':'ALREADY_APPLIED','files':0,'backup':None}
        stamp=dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'-'+uuid.uuid4().hex[:6]
        backup=root.parent/(root.name+'-before-reporting-update-'+stamp+'.zip')
        with zipfile.ZipFile(backup,'x',zipfile.ZIP_DEFLATED) as z:
            for name,data in originals.items():
                if data is not None:z.writestr(name,data)
            z.writestr('UPDATE_RECORD.json',json.dumps({'kind':'reporting-only-update','files':{n:{'before_sha256':old_hashes[n],'after_sha256':digest_bytes(changed[n])}for n in changed}},indent=2)+'\n')
        replaced=[]
        try:
            for name,data in changed.items():
                p=safe_path(root,name);p.parent.mkdir(parents=True,exist_ok=True)
                # Atomic replacement of each file; restore every earlier replacement on failure.
                fd,tmp=tempfile.mkstemp(prefix='.'+p.name+'.',dir=p.parent)
                try:
                    with os.fdopen(fd,'wb') as f:f.write(data)
                    mode=(p.stat().st_mode&0o777) if p.exists() else 0o644
                    os.chmod(tmp,mode);os.replace(tmp,p);replaced.append(name)
                finally:
                    if os.path.exists(tmp):os.unlink(tmp)
        except BaseException:
            for name in reversed(replaced):
                p=safe_path(root,name);before=originals[name]
                if before is None:p.unlink()
                else:p.write_bytes(before)
            raise
        return {'status':'APPLIED','files':len(changed),'backup':str(backup),'work':str(work)}
