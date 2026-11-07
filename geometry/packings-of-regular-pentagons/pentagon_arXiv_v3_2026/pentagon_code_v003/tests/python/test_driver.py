"""Controller and release invariants. Synthetic subprocesses are NOT OCaml runs."""
import importlib.util, json, os, signal, subprocess, sys, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('pentagon_driver',ROOT/'scripts/driver.py')
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)

class Selection(unittest.TestCase):
    def setUp(self):self.reg=json.loads((ROOT/'registry.json').read_text())
    def args(self,**kw):
        a=dict(job=None,claim=None,section=None,all=False,changed=False,diagnostics=False,tests=False,extended=False)
        a.update(kw);return SimpleNamespace(**a)
    def test_default_is_unit(self):self.assertEqual([j['id']for j in d.select_jobs(self.reg,self.args())],['unit','squeeze_sign_tests'])
    def test_changed_domains_and_contracts_plus_tests(self):
        xs=d.select_jobs(self.reg,self.args(changed=True));self.assertEqual(len(xs),19)
        self.assertEqual(sum(j.get('changed_domain',False) for j in xs),8)
    def test_claim_selects_both_branches(self):
        ids=[j['id']for j in d.select_jobs(self.reg,self.args(claim=['calc:pseudo2']))]
        self.assertEqual(set(ids),{'unit','mitm_precluster2_case0','mitm_precluster2_case1','mitm_precluster2_case2'})
    def test_all_required_count(self):
        self.assertEqual(len(d.select_jobs(self.reg,self.args(all=True))),73)
    def test_all_diagnostics_count(self):
        self.assertEqual(len(d.select_jobs(self.reg,self.args(all=True,diagnostics=True))),77)
    def test_squeeze_number_not_gamma_section(self):
        ids={j['id']for j in d.select_jobs(self.reg,self.args(claim=['6.5']))}
        self.assertNotIn('gamma_convexity',ids);self.assertIn('squeeze',ids)
        self.assertTrue({'squeeze_sign_'+x for x in ['BA_BC','BA_CB','AB_BC','AB_CB']}<=ids)
    def test_squeeze_section_and_source_code(self):
        a={j['id']for j in d.select_jobs(self.reg,self.args(section=['6.3']))}
        b={j['id']for j in d.select_jobs(self.reg,self.args(claim=['LZMJIZU']))}
        self.assertEqual(a,b)
    def test_no_duplicate_union(self):
        a=d.select_jobs(self.reg,self.args(job=['squeeze'],claim=['6.5','lemma:squeeze-area']))
        self.assertEqual(len(a),len({j['id']for j in a}))
    def test_unknown_job_fails(self):
        with self.assertRaises(ValueError):d.select_jobs(self.reg,self.args(job=['not-a-job']))
    def test_unknown_claim_fails(self):
        with self.assertRaises(ValueError):d.select_jobs(self.reg,self.args(claim=['not-a-label']))
    def test_duplicate_registry_fails(self):
        with self.assertRaises(ValueError):d.select_jobs({'jobs':[self.reg['jobs'][0]]*2},self.args())
    def test_all_excludes_diagnostics(self):
        self.assertTrue(all(j['role']!='diagnostic' for j in d.select_jobs(self.reg,self.args(all=True))))
    def test_all_contains_all_25_mitm(self):
        self.assertEqual(sum(j['id'].startswith('mitm_') for j in d.select_jobs(self.reg,self.args(all=True))),25)
    def test_proofs_require_unit(self):
        self.assertTrue(all(set(j['deps'])=={'unit','extended','squeeze_sign_tests'} for j in d.select_jobs(self.reg,self.args(all=True))if j['role']=='proof'))

class ResourceAndCache(unittest.TestCase):
    def setUp(self):self.tmp=tempfile.TemporaryDirectory();self.p=Path(self.tmp.name)/'job.log'
    def tearDown(self):self.tmp.cleanup()
    def good(self):self.p.write_text('PENTAGON STACK RETAINED: 16777216\nPENTAGON JOB PASS: x\n')
    def test_admit_empty(self):self.assertTrue(d.admission_ok(32,8,4,[]))
    def test_reserve_future_growth(self):self.assertFalse(d.admission_ok(20,8,4,[0,0,0]))
    def test_rss_not_double_counted(self):self.assertTrue(d.admission_ok(13,8,4,[4]))
    def test_exact_admission_boundary(self):self.assertTrue(d.admission_ok(12,8,4,[]))
    def test_missing_marker(self):self.p.write_text('done\n');self.assertFalse(d.scan_completion(self.p,'x')[0])
    def test_wrong_job_marker(self):self.good();self.assertFalse(d.scan_completion(self.p,'y')[0])
    def test_stack_marker_required(self):self.p.write_text('PENTAGON JOB PASS: x\n');self.assertFalse(d.scan_completion(self.p,'x')[0])
    def test_later_error_overrides_marker(self):
        self.good();self.p.write_text(self.p.read_text()+'PENTAGON JOB ERROR: Stack_overflow\n');self.assertEqual(d.scan_completion(self.p,'x')[1],'STACK_OVERFLOW')
    def test_test_failure_overrides(self):
        self.good();self.p.write_text(self.p.read_text()+'TEST FAIL [EXACT] bad\n');self.assertEqual(d.scan_completion(self.p,'x')[1],'TEST_FAILURE')
    def test_cache_intact(self):
        self.good();row=dict(status='PASS',fingerprint='a',process_exit=0,log=str(self.p),log_sha256=d.digest(self.p));self.assertTrue(d.cache_valid(row,'x','a'))
    def test_cache_changed_environment(self):
        self.good();row=dict(status='PASS',fingerprint='a',process_exit=0,log=str(self.p),log_sha256=d.digest(self.p));self.assertFalse(d.cache_valid(row,'x','b'))
    def test_cache_tampered_log(self):
        self.good();row=dict(status='PASS',fingerprint='a',process_exit=0,log=str(self.p),log_sha256=d.digest(self.p));self.p.write_text(self.p.read_text()+'changed');self.assertFalse(d.cache_valid(row,'x','a'))
    def test_cache_timeout_never_pass(self):
        self.good();row=dict(status='TIMEOUT',fingerprint='a',process_exit=0,log=str(self.p),log_sha256=d.digest(self.p));self.assertFalse(d.cache_valid(row,'x','a'))
    def test_drain_then_cancel(self):
        c=d.StopControl();c.handle(signal.SIGINT,None);self.assertTrue(c.drain);self.assertFalse(c.cancel);c.handle(signal.SIGINT,None);self.assertTrue(c.cancel)
    def test_sigterm_cancels(self):
        c=d.StopControl();c.handle(signal.SIGTERM,None);self.assertTrue(c.cancel)

class SubprocessTests(unittest.TestCase):
    def test_pass_process(self):
        with tempfile.TemporaryDirectory() as p:
            p=Path(p);j={'id':'x'};cmd=[sys.executable,'-c',"print('PENTAGON STACK RETAINED: 16777216');print('PENTAGON JOB PASS: x')"]
            r=d.Running(j,cmd,p,p/'a.log',dict(os.environ),5,512*1024**2)
            import time
            while not r.poll():time.sleep(.01)
            self.assertEqual(r.finish()['status'],'PASS')
    def test_nonzero_even_with_marker(self):
        with tempfile.TemporaryDirectory() as p:
            p=Path(p);r=d.Running({'id':'x'},[sys.executable,'-c',"print('PENTAGON STACK RETAINED: 16777216');print('PENTAGON JOB PASS: x');raise SystemExit(2)"],p,p/'a.log',dict(os.environ),5,512*1024**2)
            import time
            while not r.poll():time.sleep(.01)
            self.assertEqual(r.finish()['status'],'FAILED')
    def test_timeout_even_with_marker(self):
        with tempfile.TemporaryDirectory() as p:
            p=Path(p);r=d.Running({'id':'x'},[sys.executable,'-u','-c',"import time;print('PENTAGON STACK RETAINED: 16777216');print('PENTAGON JOB PASS: x');time.sleep(3)"],p,p/'a.log',dict(os.environ),.1,512*1024**2)
            import time
            while not r.poll():time.sleep(.01)
            self.assertEqual(r.finish()['status'],'TIMEOUT')

class SourceBindings(unittest.TestCase):
    def test_c013_actual_initializer(self):
        s=(ROOT/'ocaml/mitm-calcs.ml').read_text();p=s[s.index('let init2Cps_precluster6'):];p=p[:p.index(';;')]
        self.assertIn('aK + two * epsM_I',p);self.assertNotIn('(a >> aK + epsM_I)',p)
    def test_c014_both_use_actual_helper(self):
        s=(ROOT/'ocaml/mitm-calcs.ml').read_text()
        for name in ['precluster2_case1','precluster2_case2']:
            p=s[s.index('let '+name):];p=p[:p.index(';;')]
            self.assertIn('pseudo2_boundary_excluded dAB dBC dAC',p)
    def test_c015_independent_candidates(self):
        s=(ROOT/'ocaml/banana.ml').read_text();self.assertEqual(s.count('(if meets_global_max then [(x_gmax,y_gmax)] else []) @'),2)
    def test_no_loadtime_proof_search_ad(self):
        s=(ROOT/'ocaml/autodiff.ml').read_text()
        self.assertNotIn('\nmap (recurseD',s);self.assertIn('let twist_claim_lj1 () =',s)
    def test_previous_shadowed_test_retained(self):
        s=(ROOT/'ocaml/autodiff.ml').read_text();self.assertIn('let test_multD ()',s);self.assertIn('let test_multD2 ()',s)
    def test_no_obsolete_arithmetic(self):
        self.assertFalse((ROOT/'figure/obsolete_interval.ml').exists())
    def test_no_catch_all_empty_intersection(self):
        s=(ROOT/'ocaml/banana.ml').read_text();p=s[s.index('let someinter_I'):];p=p[:p.index(';;')]
        self.assertNotIn('with _',p);self.assertIn('disjoint_I',p)
    def test_public_source_no_handwritten_dependency(self):
        self.assertNotIn('Dimer March 2016',(ROOT/'ocaml/dimer.ml').read_text())

if __name__=='__main__':unittest.main(verbosity=2)
