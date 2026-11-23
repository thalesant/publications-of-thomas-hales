"""Reader navigation and report destination tests; no mathematical execution."""
import json,re,subprocess,unittest,tempfile
from pathlib import Path
from unittest.mock import patch
from scripts.report_paths import report_destination
ROOT=Path(__file__).resolve().parents[2]
class Documentation(unittest.TestCase):
 def test_catalog_expected_match(self):
  c=json.loads((ROOT/'mathematica/checks_catalog.json').read_text());e=json.loads((ROOT/'mathematica/expected_checks.json').read_text())
  self.assertEqual(len(c),161);self.assertEqual(set(c),set(e['required_ids']));self.assertEqual(sum(map(len,e['by_section'].values())),161)
  for k,v in c.items():
   for f in ['assertion','why','role','paper_reference','scope','section']:self.assertTrue(v[f],(k,f))
   self.assertIn(k,e['by_section'][v['section']])
 def test_mathematical_roles_present(self):
  c=json.loads((ROOT/'mathematica/checks_catalog.json').read_text());roles={v['role']for v in c.values()}
  self.assertEqual(roles,{'Paper assertion','Supporting identity','Implementation check','Numerical diagnostic'})
 def test_catalog_source_line(self):
  c=json.loads((ROOT/'mathematica/checks_catalog.json').read_text());lines=(ROOT/'mathematica/PentagonChecks.wl').read_text().splitlines()
  for k,v in c.items():self.assertIn('record["'+v['prefix']+'"',lines[v['line']-1],k)
 def test_every_job_dispatched(self):
  reg=json.loads((ROOT/'registry.json').read_text());s=(ROOT/'ocaml/jobs.ml').read_text()
  calls=re.findall(r'^  \| "([^"]+)" ->',s,re.M)
  self.assertEqual(set(calls),{j['id']for j in reg['jobs']});self.assertEqual(len(calls),len(set(calls)))
 def test_bare_number_disambiguated(self):
  jobs=json.loads((ROOT/'registry.json').read_text())['jobs']
  gamma=next(j for j in jobs if j['id']=='gamma_convexity');self.assertNotIn('6.5',gamma['aliases']);self.assertIn('Section 6.5',gamma['aliases'])
 def test_source_does_not_contain_personal_paths(self):
  for folder in ['scripts','ocaml','tests/ocaml','mathematica','environment']:
   for p in (ROOT/folder).rglob('*'):
    if p.is_file() and p.suffix in ['.py','.ml','.wl','.wls','.sh','.md']:
     self.assertNotRegex(p.read_text(),r'/home/autonomy|/Users/auton|/mnt/data/',str(p))
 def test_export_api_matches_instructions(self):
  s=(ROOT/'mathematica/PentagonChecks.wl').read_text();d=(ROOT/'mathematica/README.md').read_text()
  self.assertIn('ExportReport[file_String,report_Association]',s);self.assertIn('ExportReport[output, report]',d)
  self.assertIn('DescribeChecks[section_String]',s);self.assertIn('loadedSourceIdentity=!=sourceIdentity[]',s)
 def test_source_load_operator_environment(self):
  s=(ROOT/'ocaml/loader.ml').read_text();self.assertIn('open Stdlib;;\nlet () = pentagon_load_relative "ocaml/squeeze_sign.ml";;\nopen Pent;;',s)
  s=(ROOT/'scripts/worker.ml').read_text();self.assertIn('open Stdlib;;\nlet () = pentagon_load_relative "tests/ocaml/squeeze_tests.ml";;\nopen Pent;;',s)
 def test_windows_copy_is_optional(self):self.assertIsNone(report_destination(None))
 def test_explicit_path(self):
  with tempfile.TemporaryDirectory() as d:self.assertEqual(report_destination(d),Path(d).resolve())
 def test_windows_discovery_missing_interop(self):
  with patch('scripts.report_paths.shutil.which',return_value=None):
   with self.assertRaises(OSError):report_destination('windows-downloads')
 def test_windows_known_folder_spaces(self):
  with tempfile.TemporaryDirectory(prefix='Downloads space ')as d:
   outputs=[subprocess.CompletedProcess([],0,b'C:\\Users\\Example Name\\Downloads\r\n',b''),subprocess.CompletedProcess([],0,(d+'\n').encode(),b'')]
   with patch('scripts.report_paths.shutil.which',side_effect=lambda x:'/fake/'+x),patch('scripts.report_paths.subprocess.run',side_effect=outputs)as run:
    self.assertEqual(report_destination('windows-downloads'),Path(d));self.assertIn('shell:Downloads',run.call_args_list[0].args[0][-1])
 def test_windows_bad_multiline_rejected(self):
  with patch('scripts.report_paths.shutil.which',return_value='/fake'),patch('scripts.report_paths.subprocess.run',return_value=subprocess.CompletedProcess([],0,b'one\ntwo',b'')):
   with self.assertRaises(OSError):report_destination('windows-downloads')

if __name__=='__main__':unittest.main()
