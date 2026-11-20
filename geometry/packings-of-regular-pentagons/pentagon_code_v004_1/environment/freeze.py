#!/usr/bin/env python3
"""Preserve an explicit dependency checkout and installed metadata; no source edits.
Run after tests, not while modifying or reinstalling the selected switch.
The optional --fetch-crlibm flag asks opam to obtain its exact source for archival.
Only explicitly selected source paths and opam command outputs are collected.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,tarfile,tempfile,datetime,shutil,sys

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--interval-source',type=Path,required=True)
 ap.add_argument('--switch',default='pentagon-4.14.4')
 ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'archives')
 ap.add_argument('--fetch-crlibm',action='store_true')
 a=ap.parse_args();src=a.interval_source.expanduser().resolve()
 if not (src/'interval_crlibm.opam').is_file():ap.error('Not an interval-library source checkout: interval_crlibm.opam is missing')
 out=a.output.expanduser().resolve();out.mkdir(parents=True,exist_ok=True)
 if out==src or out.is_relative_to(src):ap.error('Output must be outside the source checkout')
 dest=out/('dependency_snapshot_'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
 dest.mkdir();manifest={'scope':'Source archive and installed metadata, not a new proof execution.','switch':a.switch}
 archive=dest/'ocaml-interval-source.tar.gz'
 with tarfile.open(archive,'w:gz') as z:
  for p in sorted(src.rglob('*')):
   rel=p.relative_to(src)
   if any(x in {'_build','.git','_opam'} for x in rel.parts):continue
   if p.is_symlink():raise RuntimeError('Symlink requires manual review before archival: '+str(p))
   if p.is_file():z.add(p,arcname='ocaml-interval/'+str(rel),recursive=False)
 manifest['interval_archive_sha256']=sha(archive)
 for name,cmd in [('installed-packages',['opam','list','--switch='+a.switch,'--installed']),('pins',['opam','pin','list','--switch='+a.switch]),('compiler',['opam','exec','--switch='+a.switch,'--','ocamlc','-config'])]:
  r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (dest/(name+'.txt')).write_text(r.stdout)
  if r.returncode:raise RuntimeError('Failed command: '+' '.join(cmd))
 subprocess.run(['opam','switch','export','--switch='+a.switch,'--full',str(dest/'switch.opam')],check=True)
 if a.fetch_crlibm:
  with tempfile.TemporaryDirectory() as t:
   checkout=Path(t)/'crlibm'
   subprocess.run(['opam','source','crlibm.0.5.1','--dir='+str(checkout)],check=True)
   arc=dest/'crlibm-0.5.1-source.tar.gz'
   with tarfile.open(arc,'w:gz') as z:z.add(checkout,arcname='crlibm-0.5.1')
   manifest['crlibm_archive_sha256']=sha(arc)
 (dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print('Saved:',dest);print('Keep this directory, including original license notices, with the released code and run reports.')
if __name__=='__main__':
 try:main()
 except Exception as e:print('FREEZE INCOMPLETE:',e,file=sys.stderr);sys.exit(1)
