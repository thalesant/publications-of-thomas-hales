"""Resolve optional report destinations without knowing a user's account or folders."""
from pathlib import Path
import shutil,subprocess

def report_destination(value) -> Path | None:
    if value is None:return None
    text=str(value)
    if text not in {'windows-downloads','auto'}:return Path(text).expanduser().resolve()
    powershell=shutil.which('powershell.exe')
    wslpath=shutil.which('wslpath')
    if not powershell or not wslpath:
        raise OSError('Windows Downloads discovery requires WSL interoperability; use an explicit Linux destination or omit --copy-report.')
    script="[Console]::OutputEncoding=[System.Text.Encoding]::UTF8; $d=(New-Object -ComObject Shell.Application).NameSpace('shell:Downloads'); if ($null -eq $d) { exit 1 }; [Console]::WriteLine($d.Self.Path)"
    p=subprocess.run([powershell,'-NoProfile','-NonInteractive','-Command',script],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
    if p.returncode:raise OSError('Windows Downloads discovery failed: '+p.stderr.decode(errors='replace').strip())
    win=p.stdout.decode('utf-8-sig').strip()
    if not win or '\n' in win or '\x00' in win:raise OSError('Invalid Windows Downloads response')
    q=subprocess.run([wslpath,'-u',win],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=15)
    if q.returncode:raise OSError('Could not translate the Windows Downloads path into a WSL path')
    dest=Path(q.stdout.decode().strip())
    if not dest.is_absolute() or not dest.is_dir():raise OSError('Discovered Downloads folder is unavailable: '+str(dest))
    return dest
