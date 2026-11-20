"""End-to-end scheduler tests with SYNTHETIC Python children, never OCaml."""
import importlib.util, json, os, sys, tempfile, unittest, zipfile
from pathlib import Path
from unittest import mock
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('driver_integration',ROOT/'scripts/driver.py')
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)

class Integration(unittest.TestCase):
 def setup_root(self,td,fail_unit=False):
  root=Path(td)/'release';root.mkdir();(root/'scripts').mkdir();(root/'ocaml').mkdir();(root/'tests/ocaml').mkdir(parents=True)
  (root/'run.py').write_text('# synthetic fixture\n')
  jobs=[dict(id='unit',role='test',claims=[],call='synthetic'),dict(id='a',role='proof',claims=['claim:a']),dict(id='b',role='proof',claims=['claim:b'])]
  (root/'registry.json').write_text(json.dumps(dict(jobs=jobs)))
  worker=root/'synthetic.py'
  worker.write_text("import os,time,sys\nj=os.environ['PENTAGON_JOB']\ntime.sleep(.15)\n"+
   ("\nif j=='unit': print('TEST FAIL synthetic');sys.exit(1)\n" if fail_unit else '')+
   "print('PENTAGON STACK RETAINED: 16777216');print('PENTAGON JOB PASS: '+j)\n")
  (root/'scripts/worker.ml').write_text('(* synthetic fixture; not evaluated *)\n')
  def env(switch,folder,root):
   folder.mkdir(parents=True,exist_ok=True)
   (folder/'environment.json').write_text(json.dumps({'synthetic':True}))
   return {'synthetic':True},[sys.executable,str(worker)],dict(os.environ)
  return root,env
 def invoke(self,root,env,work,*flags):
  with mock.patch.object(d,'ROOT',root),mock.patch.object(d,'environment',env),mock.patch.object(d,'memory_info',return_value=dict(effective_total=16*d.GIB,effective_available=16*d.GIB)):
   return d.main(['--job','a','--job','b','--jobs','2','--memory-gib','.5','--reserve-gib','0','--work',str(work),*flags])
 def test_success_cache_report_and_source_integrity(self):
  with tempfile.TemporaryDirectory() as td:
   root,env=self.setup_root(td);work=Path(td)/'runs';before=d.source_inventory(root)
   self.assertEqual(self.invoke(root,env,work),0)
   first=json.loads(next(work.glob('20*/results.json')).read_text());self.assertEqual({r['status']for r in first},{'PASS'})
   self.assertEqual(self.invoke(root,env,work),0)
   rs=sorted(work.glob('20*/results.json'));last=json.loads(rs[-1].read_text());self.assertEqual({r['status']for r in last},{'CACHED_PASS'})
   self.assertEqual(d.source_inventory(root),before)
   zs=list(work.glob('*.zip'));self.assertEqual(len(zs),2)
   with zipfile.ZipFile(zs[-1]) as z:self.assertIn('SUMMARY.md',z.namelist());self.assertIn('source/registry.json',z.namelist())
 def test_failure_blocks_proofs(self):
  with tempfile.TemporaryDirectory() as td:
   root,env=self.setup_root(td,True);work=Path(td)/'runs'
   self.assertEqual(self.invoke(root,env,work),1)
   rs=json.loads(next(work.glob('20*/results.json')).read_text());self.assertEqual({r['id']:r['status']for r in rs},{'unit':'FAILED','a':'BLOCKED','b':'BLOCKED'})
 def test_rerun_ignores_cache(self):
  with tempfile.TemporaryDirectory() as td:
   root,env=self.setup_root(td);work=Path(td)/'runs'
   self.assertEqual(self.invoke(root,env,work),0);self.assertEqual(self.invoke(root,env,work,'--rerun'),0)
   rs=json.loads(sorted(work.glob('20*/results.json'))[-1].read_text());self.assertEqual({r['status']for r in rs},{'PASS'})
 def test_small_memory_refuses_without_launch(self):
  with tempfile.TemporaryDirectory() as td:
   root,env=self.setup_root(td);work=Path(td)/'runs'
   with mock.patch.object(d,'ROOT',root),mock.patch.object(d,'environment',env),mock.patch.object(d,'memory_info',return_value=dict(effective_total=d.GIB,effective_available=d.GIB)):
    self.assertEqual(d.main(['--work',str(work)]),1)
   self.assertFalse(list(work.glob('20*/*.log')))
 def test_protected_output_directory(self):
  with tempfile.TemporaryDirectory() as td:
   root,env=self.setup_root(td)
   with mock.patch.object(d,'ROOT',root):
    with self.assertRaises(SystemExit):d.main(['--work',str(root/'ocaml'/'runs')])

if __name__=='__main__':unittest.main(verbosity=2)
