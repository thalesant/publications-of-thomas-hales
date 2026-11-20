"""Component boundaries and upgrade tests. All invented run logs are SYNTHETIC."""
from pathlib import Path
import copy, fcntl, hashlib, json, shutil, tempfile, unittest, zipfile
from scripts import verification as v
from scripts import driver
from scripts.reporting_upgrade import apply_update

ROOT=Path(__file__).resolve().parents[2]

class ComponentReports(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)/'project';self.root.mkdir()
        for d in ('mathematica','paper','verification','provenance','ocaml','scripts','tests/ocaml'):(self.root/d).mkdir(parents=True,exist_ok=True)
        for n in v.WOLFRAM_FILES:(self.root/'mathematica'/n).write_text('synthetic '+n)
        v.write_json(self.root/'mathematica/expected_checks.json',{'required_ids':['a','b'],'sections':['all']})
        (self.root/'paper/pentagon_v007.tex').write_text('synthetic paper')
        (self.root/'ocaml/test.ml').write_text('synthetic numerical definition')
        (self.root/'run.py').write_text('synthetic runner')
        (self.root/'scripts/worker.ml').write_text('synthetic worker')
        self.jobs=[{'id':n,'role':'proof','required_for_confirmation':True}for n in ('x','y')]
        v.write_json(self.root/'registry.json',{'version':'synthetic','jobs':self.jobs})
        v.write_json(self.root/'verification/association.json',{'schema':1,'manuscript':'paper/pentagon_v007.tex',
            'files':{'paper/pentagon_v007.tex':v.digest(self.root/'paper/pentagon_v007.tex')},
            'wolfram_expected_checks_sha256':v.digest(self.root/'mathematica/expected_checks.json')})
    def tearDown(self):self.tmp.cleanup()
    def report(self):
        return {'ReportSchema':2,'Component':'PentagonChecks','IdentityScope':'component-local-files',
                'SourceSHA256':v.wolfram_identity(self.root),'SectionsRun':['all'],
                'Checks':[{'ID':n,'Passed':True} for n in ('a','b')],
                'Total':2,'Failed':0,'AllRequestedChecksPassed':True,'KernelVersion':'SYNTHETIC'}
    def save_report(self,x=None):
        p=self.root/'verification/paper-checks.json';v.write_json(p,x or self.report());return p
    def legacy_report(self):
        x=self.report();x.pop('ReportSchema');x.pop('Component');x.pop('IdentityScope')
        old={n:hashlib.sha256(('old '+n).encode()).hexdigest()for n in v.LEGACY_WOLFRAM_FILES}
        x['SourceSHA256']={'mathematica/'+n:h for n,h in old.items()}
        x['SourceSHA256']['paper/old.tex']='f'*64;x['Version']='synthetic-old';x['Manuscript']='old.tex'
        compat={'wolfram':{'current_source_sha256':v.wolfram_identity(self.root),
            'legacy_reports':[{'id':'synthetic-equivalence','source_sha256':old,'basis':'SYNTHETIC test equivalence fixture'}]}}
        cp=self.root/'provenance/report-compatibility.json'
        old=v.read_json(cp) if cp.exists() else {}
        old.update(compat);v.write_json(cp,old)
        return x
    def run_record(self,legacy=False,names=('x','y'),stamp='20260101-a',env=None):
        folder=self.root/'runs'/stamp;folder.mkdir(parents=True)
        numerical=v.source_inventory(self.root);source=dict(numerical)
        if legacy:
            source.update({'paper/old.tex':'f'*64,'mathematica/old.wl':'a'*64,'scripts/verification.py':'b'*64})
            p=self.root/'provenance/report-compatibility.json';c=v.read_json(p)if p.exists()else{}
            c['ocaml_v004_source_inventory']=source;v.write_json(p,c)
        env=env or {'SYNTHETIC':True};fp=v.canonical({'source':source,'environment':env})
        v.write_json(folder/'source-sha256.json',source);v.write_json(folder/'environment/environment.json',env)
        v.write_json(folder/'fingerprint.json',{'value':fp});v.write_json(folder/'plan.json',{'jobs':[j for j in self.jobs if j['id']in names]})
        rows=[]
        for name in names:
            p=folder/(name+'.log');p.write_text('SYNTHETIC fixture\n'+v.STACK_MARKER+'\nPENTAGON JOB PASS: '+name+'\n')
            rows.append({'id':name,'status':'PASS','process_exit':0,'failure_kind':None,'fingerprint':fp,'log_sha256':v.digest(p),'wall_seconds':1.0})
        v.write_json(folder/'results.json',rows);return folder
    def test_standalone_identity_with_no_paper_or_ocaml(self):
        p=self.save_report();shutil.rmtree(self.root/'paper');shutil.rmtree(self.root/'ocaml');shutil.rmtree(self.root/'scripts')
        self.assertEqual(v.inspect_wolfram(self.root,p)['status'],'PASS')
    def test_optional_cli_is_not_a_library_dependency(self):
        p=self.save_report();optional=self.root/'mathematica/run_checks.wls'
        optional.write_text('changed optional CLI')
        self.assertEqual(v.inspect_wolfram(self.root,p)['status'],'PASS')
        optional.unlink();self.assertEqual(v.inspect_wolfram(self.root,p)['status'],'PASS')
    def test_moving_component_and_report_preserves_identity(self):
        p=self.save_report();dest=Path(self.tmp.name)/'A different machine with spaces';shutil.copytree(self.root,dest)
        shutil.rmtree(self.root);self.assertEqual(v.inspect_wolfram(dest,dest/'verification/paper-checks.json')['status'],'PASS')
    def test_changed_paper_does_not_change_components(self):
        self.run_record();p=self.save_report();old=v.source_inventory(self.root)
        (self.root/'paper/pentagon_v007.tex').write_text('changed prose')
        self.assertEqual(v.source_inventory(self.root),old);self.assertEqual(v.inspect_wolfram(self.root,p)['status'],'PASS')
        r=v.refresh(self.root);self.assertEqual(r['ocaml']['passed'],2);self.assertEqual(r['association']['status'],'ASSOCIATION_MISMATCH');self.assertFalse(r['complete'])
    def test_changed_math_does_not_invalidate_ocaml(self):
        self.run_record();old=v.source_inventory(self.root);(self.root/'mathematica/PentagonChecks.wl').write_text('different test')
        self.assertEqual(v.source_inventory(self.root),old);self.assertEqual(v.refresh(self.root)['ocaml']['passed'],2)
    def test_changed_confirmation_does_not_change_numerical_inventory(self):
        old=v.source_inventory(self.root);(self.root/'scripts/verification.py').write_text('publishing code');(self.root/'confirm.py').write_text('publishing entry')
        self.assertEqual(v.source_inventory(self.root),old)
    def test_changed_worker_invalidates_ocaml(self):
        self.run_record();(self.root/'scripts/worker.ml').write_text('different work');self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
    def test_changed_registry_invalidates_ocaml(self):
        self.run_record();p=self.root/'registry.json';p.write_text(p.read_text()+' ');self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
    def test_unknown_schema_rejected(self):
        x=self.report();x['ReportSchema']=99
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_missing_hash_is_rejected(self):
        x=self.report();x['SourceSHA256'].pop('PentagonChecks.wl')
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_boolean_total_is_not_an_integer_count(self):
        x=self.report();x['Total']=True
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_bad_record_type_rejected(self):
        x=self.report();x['Checks']=['a','b']
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_nonstrings_do_not_break_id_validation(self):
        x=self.report();x['Checks'][0]['ID']=['a']
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_legacy_import_retains_bytes_and_identity(self):
        x=self.legacy_report();p=self.save_report(x);before=p.read_bytes();r=v.import_wolfram(self.root,p)
        self.assertEqual(r['source_match']['mode'],'APPROVED_LEGACY_EQUIVALENCE')
        self.assertEqual(r['source_match']['original_manuscript'],'old.tex')
        self.assertEqual((self.root/'verification/wolfram-report.json').read_bytes(),before)
    def test_unknown_legacy_program_rejected(self):
        x=self.legacy_report();x['SourceSHA256']['mathematica/PentagonChecks.wl']='1'*64
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_changed_current_component_disables_legacy_acceptance(self):
        p=self.save_report(self.legacy_report());(self.root/'mathematica/PentagonChecks.wl').write_text('different component')
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,p)
    def test_legacy_failures_not_excused_by_equivalence(self):
        x=self.legacy_report();x['Checks'][0]['Passed']=False
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_legacy_missing_check_rejected(self):
        x=self.legacy_report();x['Checks'].pop()
        with self.assertRaises(ValueError):v.inspect_wolfram(self.root,self.save_report(x))
    def test_legacy_old_paper_hash_is_metadata_only(self):
        x=self.legacy_report();x['SourceSHA256']['paper/old.tex']='7'*64
        self.assertEqual(v.inspect_wolfram(self.root,self.save_report(x))['status'],'PASS')
    def test_exact_v004_ocaml_records_reused_without_rewriting(self):
        f=self.run_record(legacy=True);before={p.relative_to(f).as_posix():p.read_bytes()for p in f.rglob('*')if p.is_file()}
        r=v.refresh(self.root);self.assertEqual(r['ocaml']['passed'],2)
        self.assertTrue(all(x['source_match']=='V004_EXACT_NUMERICAL_COMPONENT'for x in r['ocaml']['jobs'].values()))
        self.assertEqual(before,{p.relative_to(f).as_posix():p.read_bytes()for p in f.rglob('*')if p.is_file()})
    def test_unknown_extra_legacy_file_rejected(self):
        f=self.run_record(legacy=True);p=f/'source-sha256.json';x=v.read_json(p);x['unknown.py']='8'*64;v.write_json(p,x)
        self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
    def test_changed_numerics_reject_legacy_records(self):
        self.run_record(legacy=True);(self.root/'ocaml/test.ml').write_text('changed arithmetic');self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
    def test_legacy_log_digest_still_checked(self):
        f=self.run_record(legacy=True);(f/'x.log').write_text('corrupted');self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
    def test_legacy_original_fingerprint_still_checked(self):
        f=self.run_record(legacy=True);v.write_json(f/'fingerprint.json',{'value':'wrong'});self.assertEqual(v.refresh(self.root)['ocaml']['passed'],0)
    def test_legacy_and_current_can_merge_same_environment(self):
        self.run_record(legacy=True,names=('x',));self.run_record(names=('y',),stamp='20260102-b')
        self.assertEqual(v.refresh(self.root)['ocaml']['passed'],2)
    def test_legacy_and_current_do_not_merge_different_environments(self):
        self.run_record(legacy=True,names=('x',));self.run_record(names=('y',),stamp='20260102-b',env={'different':True})
        self.assertEqual(v.refresh(self.root)['ocaml']['passed'],1)
    def test_resume_cache_matches_driver_without_editing_evidence(self):
        f=self.run_record(legacy=True);before=(f/'results.json').read_bytes();r=v.prepare_resume(self.root)
        cache=v.read_json(self.root/'runs/checkpoints.json');self.assertEqual(r['prepared'],2)
        fp=v.canonical({'source':v.source_inventory(self.root),'environment':{'SYNTHETIC':True}})
        self.assertTrue(all(driver.cache_valid(row,name,fp)for name,row in cache.items()))
        self.assertEqual((f/'results.json').read_bytes(),before)
        self.assertTrue(all(row['original_execution_fingerprint']!=fp for row in cache.values()))
    def test_resume_preserves_optional_diagnostic(self):
        self.jobs.append({'id':'diagnostic','role':'diagnostic','required_for_confirmation':False})
        v.write_json(self.root/'registry.json',{'version':'synthetic','jobs':self.jobs})
        self.run_record(legacy=True,names=('x','y','diagnostic'))
        r=v.prepare_resume(self.root);self.assertEqual(r['prepared'],3)
        self.assertIn('diagnostic',v.read_json(self.root/'runs/checkpoints.json'))
    def test_v004_complete_bundle_revalidates_after_relocation(self):
        self.run_record(legacy=True);p=self.save_report(self.legacy_report());v.import_wolfram(self.root,p)
        r=v.refresh(self.root);self.assertTrue(r['complete']);out=Path(self.tmp.name)/'bundle.zip';v.make_bundle(self.root,out,r)
        with zipfile.ZipFile(out)as z:z.extractall(Path(self.tmp.name)/'elsewhere')
        dest=Path(self.tmp.name)/'elsewhere/project';shutil.rmtree(self.root)
        self.assertTrue(v.refresh(dest)['complete'])

class Upgrade(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)/'project with spaces';self.root.mkdir()
        (self.root/'run.py').write_bytes(b'old run');(self.root/'registry.json').write_bytes(b'old registry');(self.root/'README.md').write_bytes(b'old readme')
        self.files={'README.md':b'new readme','docs/new.md':b'new doc'}
        self.old={'README.md':v.digest(self.root/'README.md'),'docs/new.md':None}
        self.protected={'run.py':v.digest(self.root/'run.py'),'registry.json':v.digest(self.root/'registry.json')}
    def tearDown(self):self.tmp.cleanup()
    def apply(self):return apply_update(self.root,self.files,self.old,self.protected)
    def test_apply_backup_and_idempotent(self):
        r=self.apply();self.assertEqual(r['status'],'APPLIED');self.assertEqual((self.root/'README.md').read_bytes(),b'new readme')
        with zipfile.ZipFile(r['backup'])as z:self.assertEqual(z.read('README.md'),b'old readme')
        self.assertEqual(self.apply()['status'],'ALREADY_APPLIED')
    def test_user_edit_refused_without_partial_change(self):
        (self.root/'README.md').write_bytes(b'user edit')
        with self.assertRaises(ValueError):self.apply()
        self.assertFalse((self.root/'docs/new.md').exists());self.assertEqual((self.root/'README.md').read_bytes(),b'user edit')
    def test_modified_numerical_input_refused(self):
        (self.root/'run.py').write_bytes(b'other')
        with self.assertRaises(ValueError):self.apply()
        self.assertEqual((self.root/'README.md').read_bytes(),b'old readme')
    def test_active_default_runner_refused(self):
        (self.root/'runs').mkdir()
        with (self.root/'runs/run.lock').open('a+')as f:
            fcntl.flock(f.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
            with self.assertRaises(ValueError):self.apply()
        self.assertEqual((self.root/'README.md').read_bytes(),b'old readme')
    def test_active_custom_work_refused(self):
        w=Path(self.tmp.name)/'custom';w.mkdir()
        with (w/'run.lock').open('a+')as f:
            fcntl.flock(f.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
            with self.assertRaises(ValueError):apply_update(self.root,self.files,self.old,self.protected,w)
    def test_symlink_refused(self):
        (self.root/'README.md').unlink();(self.root/'README.md').symlink_to(self.root/'run.py')
        with self.assertRaises(ValueError):self.apply()
    def test_unsafe_path_refused(self):
        with self.assertRaises(ValueError):apply_update(self.root,{'../x':b'x'},{'../x':None},self.protected)
    def test_runs_and_reports_are_untouched(self):
        (self.root/'runs').mkdir();(self.root/'runs/evidence.log').write_bytes(b'original execution')
        (self.root/'verification').mkdir();(self.root/'verification/paper-checks.json').write_bytes(b'original report')
        self.apply();self.assertEqual((self.root/'runs/evidence.log').read_bytes(),b'original execution')
        self.assertEqual((self.root/'verification/paper-checks.json').read_bytes(),b'original report')

class ExactProgram(unittest.TestCase):
    def test_mathematical_block_matches_record(self):
        s=(ROOT/'mathematica/PentagonChecks.wl').read_text();block=s[s.index('k=Cos[Pi/5]'):s.index('Options[RunChecks]')]
        c=v.compatibility_record(ROOT)['wolfram'];self.assertEqual(hashlib.sha256(block.encode()).hexdigest(),c['mathematical_block_sha256'])
        self.assertEqual(v.wolfram_identity(ROOT),c['current_source_sha256'])
    def test_no_parent_or_latex_runtime_dependency(self):
        for name in ['PentagonChecks.wl','run_checks.wls']:
            s=(ROOT/'mathematica'/name).read_text()
            for token in ['packageRoot','paper/','label-map.json','DirectoryName[scriptDirectory]','DirectoryName[packageDirectory]']:
                self.assertNotIn(token,s)
    def test_output_is_required_before_get(self):
        s=(ROOT/'mathematica/run_checks.wls').read_text();self.assertLess(s.index('Length[outputs]=!=1'),s.index('Get['))
        self.assertIn('FileExistsQ[out]',s)
    def test_old_ocaml_inventory_cannot_confirm_v005(self):
        compatibility = v.compatibility_record(ROOT)
        old = compatibility['ocaml_v004_source_inventory']
        current = v.source_inventory(ROOT)
        self.assertNotEqual(old['ocaml/pent.ml'], current['ocaml/pent.ml'])
        self.assertIsNone(v.match_ocaml_sources(old, current, compatibility))

if __name__=='__main__':unittest.main()
