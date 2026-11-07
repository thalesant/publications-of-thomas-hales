"""Integrity and relocation tests. Fixtures are synthetic records, NOT mathematical runs."""
import copy,json,tempfile,unittest,zipfile,shutil
from pathlib import Path
from scripts import verification as v

class Confirmation(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)/'release';self.root.mkdir()
  for d in ['ocaml','scripts','tests/ocaml','mathematica','paper','verification']: (self.root/d).mkdir(parents=True,exist_ok=True)
  self.jobs=[dict(id=x,role='proof' if x!='unit' else 'test',required_for_confirmation=True)for x in ['unit','a','b']]
  v.write_json(self.root/'registry.json',{'version':'synthetic','jobs':self.jobs})
  for f in ['run.py','confirm.py','RELEASE.json','ocaml/a.ml','scripts/worker.ml','paper/pentagon_v005.tex','paper/label-map.json','mathematica/PentagonChecks.wl','mathematica/run_checks.wls','mathematica/checks_catalog.json']:(self.root/f).write_text('synthetic fixture\n')
  v.write_json(self.root/'mathematica/expected_checks.json',{'required_ids':['x','y'],'sections':['all'],'by_section':{'all':['x','y']}})
 def tearDown(self):self.tmp.cleanup()
 def run_record(self,stamp='20260101-a',names=None,env=None,status='PASS'):
  folder=self.root/'runs'/stamp;folder.mkdir(parents=True)
  current=v.source_inventory(self.root);env=env or {'synthetic':1}
  fp=v.canonical({'source':current,'environment':env});names=names or ['unit','a','b']
  v.write_json(folder/'source-sha256.json',current);v.write_json(folder/'environment/environment.json',env)
  v.write_json(folder/'fingerprint.json',{'value':fp});v.write_json(folder/'plan.json',{'jobs':[j for j in self.jobs if j['id'] in names]})
  rows=[]
  for n in names:
   p=folder/(n+'.log');p.write_text('PENTAGON STACK RETAINED: 16777216\nPENTAGON JOB PASS: '+n+'\n')
   rows.append({'id':n,'status':status,'process_exit':0,'fingerprint':fp,'log_sha256':v.digest(p),'failure_kind':None,'wall_seconds':1})
  v.write_json(folder/'results.json',rows);return folder
 def wf(self):
  p=self.root/'verification/wolfram-report.json'
  x={'SourceSHA256':v.wolfram_identity(self.root),'SectionsRun':['all'],'Checks':[{'ID':n,'Passed':True}for n in ['x','y']],
     'Total':2,'Failed':0,'AllRequestedChecksPassed':True,'KernelVersion':'synthetic'}
  v.write_json(p,x);return p
 def mutate_rows(self,folder,action):
  rows=v.read_json(folder/'results.json');action(rows);v.write_json(folder/'results.json',rows)
 def test_absent_logs_not_complete(self):self.assertFalse(v.refresh(self.root)['complete'])
 def test_ocaml_alone_not_combined(self):self.run_record();x=v.refresh(self.root);self.assertEqual(x['ocaml']['status'],'COMPLETE');self.assertFalse(x['complete'])
 def test_complete_both(self):self.run_record();self.wf();self.assertTrue(v.refresh(self.root)['complete'])
 def test_missing_required_job(self):self.run_record(names=['unit','a']);self.wf();self.assertEqual(v.refresh(self.root)['ocaml']['passed'],2)
 def test_exit_nonzero_not_pass(self):
  p=self.run_record();self.mutate_rows(p,lambda xs:xs[0].update(process_exit=1));self.assertFalse(v.refresh(self.root)['complete']);self.assertTrue(v.refresh(self.root)['validation_notes'])
 def test_tampered_log(self):
  p=self.run_record();(p/'a.log').write_text('altered');self.wf();self.assertFalse(v.refresh(self.root)['complete'])
 def test_missing_marker(self):
  p=self.run_record();log=p/'a.log';log.write_text('PENTAGON STACK RETAINED: 16777216\n');self.mutate_rows(p,lambda xs:xs[1].update(log_sha256=v.digest(log)));self.assertFalse(v.refresh(self.root)['complete'])
 def test_error_after_marker(self):
  p=self.run_record();log=p/'a.log';log.write_text(log.read_text()+'TEST FAIL fixture\n');self.mutate_rows(p,lambda xs:xs[1].update(log_sha256=v.digest(log)));self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
 def test_duplicate_results(self):
  p=self.run_record();self.mutate_rows(p,lambda xs:xs.append(xs[0]));self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
 def test_wrong_fingerprint(self):
  p=self.run_record();v.write_json(p/'fingerprint.json',{'value':'bad'});self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
 def test_changed_source_invalidates_old(self):
  self.run_record();(self.root/'ocaml/a.ml').write_text('different');self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
 def test_two_environments_not_merged(self):
  self.run_record('20260101-a',['unit','a'],{'e':1});self.run_record('20260102-b',['b'],{'e':2});self.assertEqual(v.refresh(self.root)['ocaml']['passed'],2)
 def test_same_environment_disjoint_runs_combine(self):
  self.run_record('20260101-a',['unit','a']);self.run_record('20260102-b',['b']);self.assertEqual(v.refresh(self.root)['ocaml']['passed'],3)
 def test_new_failure_supersedes_old(self):
  self.run_record('20260101-a');self.run_record('20260102-b',['b'],status='TIMEOUT');self.assertEqual(v.refresh(self.root)['ocaml']['passed'],2)
 def test_cached_requires_intact_log(self):
  p=self.run_record(status='CACHED_PASS');self.wf();self.assertTrue(v.refresh(self.root)['complete']);(p/'b.log').unlink();self.assertFalse(v.refresh(self.root)['complete'])
 def test_partial_wolfram_rejected(self):
  p=self.wf();x=v.read_json(p);x['Checks'].pop();v.write_json(p,x)
  with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
 def test_duplicate_wolfram_rejected(self):
  p=self.wf();x=v.read_json(p);x['Checks'][1]=x['Checks'][0];v.write_json(p,x)
  with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
 def test_false_wolfram_rejected(self):
  p=self.wf();x=v.read_json(p);x['Checks'][1]['Passed']=False;v.write_json(p,x)
  with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
 def test_wrong_wolfram_section_rejected(self):
  p=self.wf();x=v.read_json(p);x['SectionsRun']=[];v.write_json(p,x)
  with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
 def test_changed_wolfram_source_rejected(self):
  p=self.wf();(self.root/'mathematica/PentagonChecks.wl').write_text('changed')
  with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
 def test_wrong_wolfram_summary_rejected(self):
  p=self.wf();x=v.read_json(p);x['Total']=0;v.write_json(p,x)
  with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
 def test_import_wolfram_elsewhere(self):
  p=self.wf();q=Path(self.tmp.name)/'new.json';shutil.move(p,q);v.import_wolfram(self.root,q);self.assertTrue(p.exists())
 def test_incomplete_bundle_refused(self):
  with self.assertRaises(ValueError):v.make_bundle(self.root,Path(self.tmp.name)/'bad.zip',v.refresh(self.root))
 def test_verified_bundle_revalidates_after_move(self):
  self.run_record();self.wf();rec=v.refresh(self.root);out=v.make_bundle(self.root,Path(self.tmp.name)/'checked.zip',rec)
  dest=Path(self.tmp.name)/'different';dest.mkdir()
  with zipfile.ZipFile(out)as z:z.extractall(dest)
  relocated=dest/'release';shutil.rmtree(self.root)
  self.assertTrue(v.refresh(relocated)['complete'])
 def test_bundle_never_overwrites(self):
  self.run_record();self.wf();rec=v.refresh(self.root);out=Path(self.tmp.name)/'x.zip';out.write_bytes(b'old')
  with self.assertRaises(FileExistsError):v.make_bundle(self.root,out,rec)
  self.assertEqual(out.read_bytes(),b'old')
 def test_copied_records_are_valid_without_saved_absolute_log_paths(self):
  p=self.run_record();rows=v.read_json(p/'results.json')
  for r in rows:r['log']='/no/such/file.log'
  v.write_json(p/'results.json',rows);self.assertEqual(v.refresh(self.root)['ocaml']['passed'],3)
 def test_unknown_job_does_not_count(self):
  p=self.run_record();self.mutate_rows(p,lambda xs:xs[0].update(id='unknown'));self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)

if __name__=='__main__':unittest.main()
