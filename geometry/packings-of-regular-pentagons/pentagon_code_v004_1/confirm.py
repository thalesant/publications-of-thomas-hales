#!/usr/bin/env python3
"""Inspect source-matching confirmation, import a Wolfram report, or package verified results.
Run in the extracted package; no calculations are launched by this command.
"""
from pathlib import Path
import argparse,sys
from scripts.verification import refresh, import_wolfram, make_bundle, prepare_resume
ROOT=Path(__file__).resolve().parent

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work',type=Path,help='Run directory used with run.py --work (default: package/runs)')
    p.add_argument('--wolfram',type=Path,help='Import a complete standalone or explicitly compatible legacy Wolfram report')
    p.add_argument('--check',action='store_true',help='Exit nonzero unless both OCaml and Wolfram have complete matching records')
    p.add_argument('--bundle',type=Path,help='Write a new verified distribution ZIP; requires complete matching records')
    p.add_argument('--prepare-resume',action='store_true',help='Rebuild mutable checkpoints from validated records; never run calculations')
    a=p.parse_args(argv)
    try:
        if a.wolfram:
            import_wolfram(ROOT,a.wolfram.expanduser())
        elif (ROOT/'verification/paper-checks.json').is_file():
            # A transferred component report is supported. Validate
            # it, rather than relying on the user to remember an import step.
            import_wolfram(ROOT,ROOT/'verification/paper-checks.json')
        if a.prepare_resume:
            import fcntl
            work=(a.work or ROOT/'runs').expanduser().resolve();work.mkdir(parents=True,exist_ok=True)
            with (work/'run.lock').open('a+') as lock:
                try:fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
                except BlockingIOError:raise ValueError('A runner is active; do not change checkpoints until it finishes')
                prepared=prepare_resume(ROOT,work)
            print('Validated checkpoint entries: '+str(prepared['prepared']))
        value=refresh(ROOT,a.work)
        print('OCaml: %s (%d/%d)'%(value['ocaml']['status'],value['ocaml']['passed'],value['ocaml']['required']))
        print('Wolfram: '+value['wolfram']['status'])
        print('Manuscript association: '+value['association']['status'])
        mode=value['wolfram'].get('source_match',{}).get('mode')
        if mode:print('Wolfram evidence: '+mode)
        print('Record: '+str(ROOT/'verification/CONFIRMATION.md'))
        if a.bundle:print('Verified distribution: '+str(make_bundle(ROOT,a.bundle,value)))
        return 0 if not a.check or value['complete'] else 1
    except (OSError,ValueError,KeyError,TypeError) as e:
        print('Confirmation not accepted: '+str(e),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
