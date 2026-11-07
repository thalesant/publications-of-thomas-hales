#!/usr/bin/env python3
"""Inspect source-matching confirmation, import a Wolfram report, or package verified results.
Run in the extracted package; no calculations are launched by this command.
"""
from pathlib import Path
import argparse,sys
from scripts.verification import refresh, import_wolfram, make_bundle
ROOT=Path(__file__).resolve().parent

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work',type=Path,help='Run directory used with run.py --work (default: package/runs)')
    p.add_argument('--wolfram',type=Path,help='Import the full report exported by this package’s Wolfram suite')
    p.add_argument('--check',action='store_true',help='Exit nonzero unless both OCaml and Wolfram have complete matching records')
    p.add_argument('--bundle',type=Path,help='Write a new verified distribution ZIP; requires complete matching records')
    a=p.parse_args(argv)
    try:
        if a.wolfram:import_wolfram(ROOT,a.wolfram.expanduser())
        value=refresh(ROOT,a.work)
        print('OCaml: %s (%d/%d)'%(value['ocaml']['status'],value['ocaml']['passed'],value['ocaml']['required']))
        print('Wolfram: '+value['wolfram']['status'])
        print('Record: '+str(ROOT/'verification/CONFIRMATION.md'))
        if a.bundle:print('Verified distribution: '+str(make_bundle(ROOT,a.bundle,value)))
        return 0 if not a.check or value['complete'] else 1
    except (OSError,ValueError,KeyError,TypeError) as e:
        print('Confirmation not accepted: '+str(e),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
