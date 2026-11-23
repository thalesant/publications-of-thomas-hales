"""Consolidation/scheduling tests; child programs and run records are synthetic.

These tests do not execute OCaml or assert that any mathematical search passed.
"""
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

from scripts import driver as d
from scripts import verification as v
from scripts import check_release as cr

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('confirmation_cli', ROOT/'confirm.py')
cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cli)

class Scheduling(unittest.TestCase):
    def fixture(self):
        return [dict(id=i,role=role,estimated_seconds=t) for i,role,t in
                [('short','proof',1),('unit','test',0.1),('diagnostic','diagnostic',9999),
                 ('long','proof',99),('extended','test',0.1),
                 ('squeeze_sign_tests','test',0.1),('mitm_geometric_control','test',0.1),
                 ('middle','proof',10)]]
    def test_longest_first(self):
        self.assertEqual([j['id'] for j in d.schedule_jobs(self.fixture())],
                         list(d.TEST_ORDER)+['long','middle','short','diagnostic'])
    def test_registry_option_keeps_gates_first(self):
        self.assertEqual([j['id'] for j in d.schedule_jobs(self.fixture(),'registry')],
                         list(d.TEST_ORDER)+['short','long','middle','diagnostic'])
    def test_equal_estimates_stable(self):
        j=[dict(id=n,role='proof',estimated_seconds=1)for n in ['z','a']]
        self.assertEqual([x['id']for x in d.schedule_jobs(j)],['z','a'])
    def test_bad_estimate_refused(self):
        for value in [-1,float('nan'),float('inf')]:
            with self.subTest(value=value),self.assertRaises(ValueError):
                d.schedule_jobs([dict(id='x',role='proof',estimated_seconds=value)])
    def test_unknown_order(self):
        with self.assertRaises(ValueError):d.schedule_jobs(self.fixture(),'random')
    def test_31gib_defaults_five(self):
        self.assertEqual(d.worker_limit('auto',31*d.GIB,4*d.GIB,8*d.GIB,24),5)
    def test_40gib_defaults_eight(self):
        self.assertEqual(d.worker_limit('auto',40*d.GIB,4*d.GIB,8*d.GIB,24),8)
    def test_cpu_limit(self):
        self.assertEqual(d.worker_limit('auto',128*d.GIB,4*d.GIB,8*d.GIB,3),3)
    def test_auto_ceiling(self):
        self.assertEqual(d.worker_limit('auto',256*d.GIB,4*d.GIB,8*d.GIB,64),8)
    def test_explicit_count(self):
        self.assertEqual(d.worker_limit('6',31*d.GIB,4*d.GIB,8*d.GIB,24),6)
        self.assertFalse(d.admission_ok(29*d.GIB,8*d.GIB,4*d.GIB,[0]*5))
    def test_invalid_worker_count(self):
        for value in ['0','-1','none']:
            with self.subTest(value=value),self.assertRaises(ValueError):
                d.worker_limit(value,31*d.GIB,4*d.GIB,8*d.GIB,24)
    def test_release_first_proof_is_6d(self):
        reg=json.loads((ROOT/'registry.json').read_text())
        xs=d.schedule_jobs(reg['jobs'])
        self.assertEqual(next(x['id']for x in xs if x['role']=='proof'),'mitm_calc_pent3_6D_postcluster')
    def test_new_cases_have_same_main_dispatch(self):
        jobs={x['id']:x for x in json.loads((ROOT/'registry.json').read_text())['jobs']}
        dispatch=(ROOT/'ocaml/jobs.ml').read_text()
        for name in ['pintab_area','small3C_area','face_lj1','mitm_geometric_control']:
            self.assertTrue(jobs[name]['required_for_confirmation'])
            self.assertIn('"'+name+'" ->',dispatch)
    def test_geometric_control_is_test_not_exclusion(self):
        jobs={x['id']:x for x in json.loads((ROOT/'registry.json').read_text())['jobs']}
        self.assertEqual(jobs['mitm_geometric_control']['role'],'test')
    def test_direct_crlibm_loader(self):
        source=(ROOT/'ocaml/loader.ml').read_text()
        self.assertIn('#require "interval_crlibm";;',source)
        self.assertNotIn('#require "interval.top"',source)
        self.assertIn('interval_crlibm.1.6',(ROOT/'environment/install.sh').read_text())
    def test_single_current_manuscript(self):
        self.assertEqual([p.name for p in (ROOT/'paper').glob('pentagon_v*.tex')],['pentagon_v008.tex'])
        self.assertFalse((ROOT/'supplements').exists())
        self.assertFalse((ROOT/'paper/v007').exists())
        self.assertFalse((ROOT/'docs/v007').exists())
        self.assertTrue((ROOT/'docs/pentagon_changes_2016v2_to_v007.md').is_file())

class ActualParallelController(unittest.TestCase):
    def test_five_processes_longest_first_and_geometric_gate(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)/'release';root.mkdir()
            for s in ['ocaml','scripts','tests/ocaml']:(root/s).mkdir(parents=True,exist_ok=True)
            (root/'run.py').write_text('# synthetic\n');(root/'scripts/worker.ml').write_text('synthetic\n')
            jobs=[dict(id=n,role='test',required_for_confirmation=True)for n in d.TEST_ORDER]
            # Deliberately register the longest proof last.
            jobs += [dict(id=f'p{n}',role='proof',required_for_confirmation=True,estimated_seconds=n)for n in range(1,7)]
            (root/'registry.json').write_text(json.dumps({'version':'synthetic','jobs':jobs}))
            worker=root/'synthetic.py'
            worker.write_text("import os,time\nj=os.environ['PENTAGON_JOB']\ntime.sleep(.4)\nprint('PENTAGON STACK RETAINED: 16777216')\nprint('PENTAGON JOB PASS: '+j)\n")
            def env(switch,folder,root):
                folder.mkdir(parents=True,exist_ok=True)
                (folder/'environment.json').write_text('{"synthetic":true}')
                return {'synthetic':True},[sys.executable,str(worker)],dict(os.environ)
            seen=[];counts=[];active=set();original=d.Running
            class Recording(original):
                def __init__(self,job,*a,**kw):
                    seen.append(job['id']);active.add(job['id']);counts.append(len(active))
                    super().__init__(job,*a,**kw)
                def finish(self):
                    row=super().finish();active.remove(self.job['id']);return row
            memory=dict(effective_total=31*d.GIB,effective_available=29*d.GIB)
            with mock.patch.object(d,'ROOT',root),mock.patch.object(d,'environment',env),mock.patch.object(d,'Running',Recording),mock.patch.object(d,'memory_info',return_value=memory),mock.patch.object(d,'available_cpus',return_value=24):
                self.assertEqual(d.main(['--all']),0)
            self.assertEqual(seen[:4],list(d.TEST_ORDER))
            self.assertEqual(seen[4:],['p6','p5','p4','p3','p2','p1'])
            self.assertEqual(max(counts),5)
            folder=next((root/'runs').glob('20*'))
            self.assertEqual(len(json.loads((folder/'results.json').read_text())),10)
            self.assertEqual(v.refresh(root)['ocaml']['passed'],10)
            self.assertEqual(v.refresh(root)['ocaml']['required'],10)

class AutomaticImport(unittest.TestCase):
    def fixture(self,root):
        for folder in ['mathematica','paper','verification']:(root/folder).mkdir(parents=True)
        for name in ['PentagonChecks.wl','run_checks.wls','checks_catalog.json']:(root/'mathematica'/name).write_text('synthetic\n')
        for name in ['pentagon_v007.tex','label-map.json']:(root/'paper'/name).write_text('synthetic\n')
        (root/'mathematica/expected_checks.json').write_text(json.dumps({'required_ids':['a'],'sections':['x']}))
        report={'ReportSchema':2,'Component':'PentagonChecks','IdentityScope':'component-local-files','SourceSHA256':v.wolfram_identity(root),'SectionsRun':['x'],'Checks':[{'ID':'a','Passed':True}],
                'Total':1,'Failed':0,'AllRequestedChecksPassed':True,'KernelVersion':'synthetic'}
        p=root/'verification/paper-checks.json';p.write_text(json.dumps(report));return p
    def record(self):return {'ocaml':{'status':'COMPLETE','passed':77,'required':77},'wolfram':{'status':'PASS'},'association':{'status':'MATCH'},'complete':True}
    def test_standard_transferred_report_auto_import(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td);p=self.fixture(root)
            with mock.patch.object(cli,'ROOT',root),mock.patch.object(cli,'refresh',return_value=self.record()):
                self.assertEqual(cli.main(['--check']),0)
            self.assertEqual(p.read_bytes(),(root/'verification/wolfram-report.json').read_bytes())
    def test_bad_transferred_report_does_not_replace_accepted(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td);p=self.fixture(root);v.import_wolfram(root,p)
            dest=root/'verification/wolfram-report.json';good=dest.read_bytes()
            x=json.loads(p.read_text());x['Checks'][0]['Passed']=False;p.write_text(json.dumps(x))
            with mock.patch.object(cli,'ROOT',root),mock.patch.object(cli,'refresh')as refresh:
                self.assertEqual(cli.main(['--check']),1);refresh.assert_not_called()
            self.assertEqual(dest.read_bytes(),good)
    def test_explicit_report_wins_over_stale_standard(self):
        with tempfile.TemporaryDirectory()as td:
            root=Path(td);p=self.fixture(root);q=root/'valid.json';q.write_bytes(p.read_bytes());p.write_text('{}')
            with mock.patch.object(cli,'ROOT',root),mock.patch.object(cli,'refresh',return_value=self.record()):
                self.assertEqual(cli.main(['--wolfram',str(q),'--check']),0)
            self.assertEqual(q.read_bytes(),(root/'verification/wolfram-report.json').read_bytes())

class FixedManifest(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        (self.root/'readme.txt').write_text('fixture\n');self.write()
    def tearDown(self):self.tmp.cleanup()
    def write(self, files=None):
        files=files or {'readme.txt':cr.digest(self.root/'readme.txt')}
        (self.root/'MANIFEST.json').write_text(json.dumps({'files':files}))
        (self.root/'SHA256SUMS').write_text(''.join(f'{sha}  {name}\n'for name,sha in files.items())+cr.digest(self.root/'MANIFEST.json')+'  MANIFEST.json\n')
    def test_correct(self):self.assertEqual(cr.verify(self.root),(1,[]))
    def test_changed(self):
        (self.root/'readme.txt').write_text('changed');self.assertIn('Changed file: readme.txt',cr.verify(self.root)[1])
    def test_missing(self):
        (self.root/'readme.txt').unlink();self.assertIn('Missing file: readme.txt',cr.verify(self.root)[1])
    def test_extra_run_output_allowed(self):
        (self.root/'runs').mkdir();(self.root/'runs/output.log').write_text('fixture');self.assertEqual(cr.verify(self.root),(1,[]))
    def test_json_tampering_detected(self):
        p=self.root/'MANIFEST.json';p.write_text(p.read_text()+' ')
        self.assertIn('SHA256SUMS does not match MANIFEST.json',cr.verify(self.root)[1])
    def test_duplicate_text_entry_rejected(self):
        p=self.root/'SHA256SUMS';p.write_text(p.read_text()+p.read_text().splitlines()[0]+'\n')
        with self.assertRaises(ValueError):cr.verify(self.root)
    def test_traversal_rejected(self):
        self.write({'../outside':'a'*64})
        with self.assertRaises(ValueError):cr.verify(self.root)
    def test_symlink_rejected(self):
        (self.root/'readme.txt').rename(self.root/'actual.txt');(self.root/'readme.txt').symlink_to('actual.txt')
        self.assertIn('Symlink is not a fixed release file: readme.txt',cr.verify(self.root)[1])

if __name__=='__main__':unittest.main()
