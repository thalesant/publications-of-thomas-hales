"""Static release checks, not OCaml/Wolfram execution or proof certification."""
from pathlib import Path
import hashlib,json,re,unittest
ROOT=Path(__file__).resolve().parents[2]

def strip_strings_comments(text):
    out=[];i=0;depth=0;quoted=False
    while i<len(text):
        if depth:
            if text.startswith('(*',i):depth+=1;i+=2
            elif text.startswith('*)',i):depth-=1;i+=2
            else:i+=1
        elif quoted:
            if text[i]=='\\':i+=2
            elif text[i]=='"':quoted=False;i+=1
            else:i+=1
        elif text.startswith('(*',i):depth=1;i+=2
        elif text[i]=='"':quoted=True;i+=1
        else:out.append(text[i]);i+=1
    if depth or quoted:raise ValueError('Unclosed comment/string')
    return ''.join(out)

class Release(unittest.TestCase):
 def test_manuscript_has_no_active_review_markup(self):
    text=(ROOT/'paper/pentagon_v005.tex').read_text()
    active='\n'.join(x for x in text.splitlines() if not x.lstrip().startswith('%'))
    self.assertNotIn('pentagonrefereenote',active);self.assertNotIn('pentagonproposal',active)
    self.assertNotIn('TODO',active)
 def test_label_number_comparison(self):
    record=json.loads((ROOT/'provenance/label-comparison.json').read_text())
    labels=json.loads((ROOT/'paper/label-map.json').read_text())
    self.assertEqual(len(labels),169)
    self.assertTrue(record)
 def test_navigation_codes_are_unique(self):
    x=json.loads((ROOT/'provenance/input-identities.json').read_text())['seven_letter_identifiers']
    self.assertEqual(len(x),len(set(x.values())))
    self.assertTrue(all(re.fullmatch('[A-Z]{7}',v)for v in x.values()))
    text=(ROOT/'paper/pentagon_v005.tex').read_text()
    self.assertTrue(all(v in text for v in x.values()))
 def test_wolfram_balanced_delimiters(self):
    for fn in ['mathematica/PentagonChecks.wl','mathematica/run_checks.wls','figures/PentagonFigures.wl']:
      s=strip_strings_comments((ROOT/fn).read_text());stack=[];ends={')':'(',']':'[','}':'{'}
      for c in s:
        if c in '([{':stack.append(c)
        elif c in ends:self.assertTrue(stack,fn);self.assertEqual(stack.pop(),ends[c],fn)
      self.assertEqual(stack,[],fn)
 def test_wolfram_paper_labels_exist(self):
    s=(ROOT/'mathematica/PentagonChecks.wl').read_text();labels=json.loads((ROOT/'paper/label-map.json').read_text())
    names=set(re.findall(r'"((?:sec|lemma|calc|eqn|cor):[^" ]+)"',s));self.assertTrue(names);self.assertFalse(names-set(labels))
 def test_c013_and_c014_production_calls(self):
    s=(ROOT/'ocaml/mitm-calcs.ml').read_text();self.assertIn('(a >> aK + two * epsM_I)',s)
    self.assertEqual(len(re.findall(r'pseudo2_boundary_excluded dAB dBC dAC',s)),3) # definition and two actual callers
 def test_no_source_changes_in_licenced_lib(self):
    old=json.loads((ROOT/'provenance/source_baseline.json').read_text())['lib.ml'];self.assertEqual(hashlib.sha256((ROOT/'ocaml/lib.ml').read_bytes()).hexdigest(),old)
 def test_exact_source_anchor_ranges(self):
    sm=json.loads((ROOT/'docs/source-map.json').read_text())
    for v in sm.values():
      ls=(ROOT/v['file']).read_text().splitlines();self.assertGreater(v['start'],0);self.assertGreaterEqual(v['end'],v['start']);self.assertLessEqual(v['end'],len(ls)+1)
      self.assertRegex(ls[v['start']-1],r'\blet(?: rec)? '+re.escape(v['function'])+r'(?=\s|\(|=|:|$)')
 def test_required_set_and_no_static_release_pass(self):
    reg=json.loads((ROOT/'registry.json').read_text());self.assertEqual(reg['version'],'pentagon_code_v003')
    self.assertEqual(sum(j['required_for_confirmation']for j in reg['jobs']),73)
    self.assertFalse(any('release_status'in j for j in reg['jobs']))
 def test_mathematical_source_equivalence_record(self):
    checks=json.loads((ROOT/'provenance/mathematical-source-equivalence.json').read_text())
    self.assertGreater(len(checks),8)
    self.assertTrue(all(c['noncomment_tokens_identical']for c in checks))
 def test_no_unsafe_graphics_interval(self):
    self.assertFalse((ROOT/'figure/obsolete_interval.ml').exists());self.assertNotIn('obsolete_interval',(ROOT/'ocaml/loader.ml').read_text())
 def test_static_tests_not_claimed_as_ocaml_runs(self):
    self.assertIn('synthetic',(ROOT/'tests/python/test_integration.py').read_text().lower())
    self.assertIn('not executions of OCaml',(ROOT/'docs/code_commentary.tex').read_text())

if __name__=='__main__':unittest.main(verbosity=2)
