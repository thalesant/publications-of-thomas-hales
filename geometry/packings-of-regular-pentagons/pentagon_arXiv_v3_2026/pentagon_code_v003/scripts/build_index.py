#!/usr/bin/env python3
"""Generate reader-facing offline indices from mathematical descriptions and job metadata.
Run with Python at any working directory. No proof calculations are executed.
"""
from pathlib import Path
import html,json,re
R=Path(__file__).resolve().parents[1]
E=lambda x:html.escape(str(x))
STYLE='''body{max-width:1100px;margin:35px auto;padding:0 22px;font:17px/1.55 system-ui;color:#1e2f3d}h1,h2,h3{color:#193d50}table{border-collapse:collapse;width:100%;font-size:14px}td,th{padding:9px;border-bottom:1px solid #cbd6dc;text-align:left;vertical-align:top}code,pre{font:13px/1.55 ui-monospace,monospace}pre{background:#f3f5f6;padding:14px;white-space:pre-wrap;overflow-wrap:anywhere}details{margin:12px 0}summary{cursor:pointer;font-weight:600}a{color:#075c87}input{box-sizing:border-box;width:100%;padding:10px;font-size:17px}article{border-top:1px solid #c4d3db;padding:20px 0}.tag{display:inline-block;padding:3px 8px;margin:3px;background:#eaf0f3;font-size:13px}.context{padding:14px;background:#f2f5f7}'''
def page(title):return ['<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+E(title)+'</title><style>'+STYLE+'</style></head><body><h1>'+E(title)+'</h1>']
SEARCH='''<script>document.getElementById('search').addEventListener('input',function(){const q=this.value.toLowerCase();document.querySelectorAll('article[data-search]').forEach(e=>{e.hidden=!e.dataset.search.toLowerCase().includes(q)});});</script>'''
def main():
 reg=json.loads((R/'registry.json').read_text());jobs={j['id']:j for j in reg['jobs']}
 entries=json.loads((R/'docs/claims.json').read_text());sm=json.loads((R/'docs/source-map.json').read_text())
 labs=json.loads((R/'paper/label-map.json').read_text())
 md=['# Paper-to-code index — code v003 / manuscript v005','','**Context:** commands below are for Linux/Ubuntu-WSL Bash, at the extracted package root containing `run.py`. Append `--list` to preview without executing.','',
     'The selected jobs establish their encoded terminal exclusions. The paper supplies the reductions and earlier lemmas; a claim selection is not the entire transitive mathematical proof. Use `--all` for the complete proof-job set. Source-specific completion is generated in `verification/CONFIRMATION.md`.','']
 h=page('Pentagon paper-to-code index — v003')
 h+=['<p>Companion to <a href="../paper/pentagon_v005.pdf">the paper</a>. <a href="code_commentary.pdf">Mathematical commentary</a> · <a href="RUNNING.md">Execution guide</a> · <a href="wolfram_checks.html">Wolfram checks</a> · <a href="../verification/CONFIRMATION.md">Generated confirmation</a>.</p>',
     '<div class="context"><strong>First-time reader:</strong> find a printed lemma number here, read its assumptions and cases, then inspect the indicated original function. Commands use <strong>Bash at the extracted package root</strong>, not the docs folder or a language prompt. Append <code>--list</code> to preview. A source code is a navigation key, not an additional mathematical hypothesis.</div>',
     '<p>Execution evidence is maintained separately from this fixed mathematical explanation. An absent, interrupted, or mismatched run is never represented as a pass. See <a href="VERIFICATION.md">confirmation rules</a>.</p>',
     '<input id="search" aria-label="Search calculation" placeholder="Search lemma/section number, label, seven-letter code or function">',
     '<table><tr><th>Paper</th><th>Assertion / source code</th><th>Direct jobs</th></tr>']
 for e in entries:
  if re.fullmatch('[A-Z]{7}',e['id']):h.append('<tr><td>Lemma '+E(e['number'])+'</td><td><a href="#'+E(e['id'])+'">'+E(e['comment_id'])+'</a> · '+E(e['claim'])+'</td><td>'+E(', '.join(e['jobs']))+'</td></tr>')
 h.append('</table>')
 for e in entries:
  kind='Section' if (e['label'] or '').startswith(('sec:','sub:','appendix:')) else 'Lemma'
  title=((kind+' '+e['number']+' — ')if e['number'] else '')+e['title']
  cmd='python3 run.py --claim '+(e.get('label') or e['jobs'][0])
  if not e.get('label'):cmd='python3 run.py --job '+e['jobs'][0]
  note=e.get('note','');assumptions=' '.join(e['assumptions'])
  md+=['## '+title,'','Source code: `'+str(e.get('comment_id') or e['id'])+'`; paper label: `'+str(e['label'] or '(diagnostic)')+'`.','',e['claim'],'','**Assumptions / reductions:** '+assumptions,'','**Interpretation:** '+note,'','| Job | Mathematical call | Source | Role |','|---|---|---|---|']
  h.append('<article id="'+E(e['id'])+'" data-search="'+E(title+' '+e['id']+' '+str(e['label'])+' '+str(e.get('comment_id'))+' '+' '.join(e['jobs']))+'"><h2>'+E(title)+'</h2><p><span class="tag">'+E(e.get('comment_id') or e['id'])+'</span> <code>'+E(e['label'] or 'Diagnostic')+'</code></p><p>'+E(e['claim'])+'</p><p><strong>Assumptions and preparation:</strong> '+E(assumptions)+'</p><p><strong>Interpretation:</strong> '+E(note)+'</p>')
  for jid in e['jobs']:
   j=jobs[jid];path=j.get('source','');call=j['call']
   md.append('| `'+jid+'` | `'+call+'` | `'+path+'` | '+j['role']+' |')
   h.append('<details><summary>'+E(jid)+' — '+E(j['role'])+'</summary><p>'+E(j['description'])+'</p><p>Source: <a href="../'+E(path)+'">'+E(path)+'</a>.</p><pre>'+E(call)+'</pre>')
   name=''
   if jid.startswith('mitm_'):name=jid[5:]
   elif re.search(r'(Dimer|Autodiff)\.(\w+)',call):name=re.search(r'(Dimer|Autodiff)\.(\w+)',call)[2]
   elif jid.startswith('squeeze_sign_'):name='verify_case'
   else:name={'onedeltajmin':'onedeltajamin'}.get(jid,'')
   candidate=next((v for v in sm.values()if v['function']==name and v['file']==path),None)
   if candidate:
    ls=(R/path).read_text().splitlines();a=candidate['start'];b=candidate['end'];snippet='\n'.join(f'{i+1:4}  {ls[i]}'for i in range(a-1,min(b,len(ls))))
    h.append('<p>Function <code>'+E(name)+'</code>, lines '+str(a)+'–'+str(b)+'.</p><pre>'+E(snippet)+'</pre>')
   h.append('</details>')
  md+=['','**Bash at PACKAGE_ROOT:**','```bash',cmd+' --list',cmd,'```','']
  h.append('<details><summary>Run this computational association</summary><p>In Linux/Ubuntu-WSL Bash at PACKAGE_ROOT. First command previews; second executes or reuses valid checkpoints.</p><pre>'+E(cmd+' --list\n'+cmd)+'</pre><p>Add <code>--copy-report windows-downloads</code> on WSL to copy the report to the discovered Downloads folder.</p></details></article>')
 md+=['## Complete job catalogue','','This includes supporting stages and optional diagnostics, not only the eight principal lemmas.','','| Job | Role | Paper | Mathematical task |','|---|---|---|---|']
 for j in jobs.values():md.append('| `'+j['id']+'` | '+j['role']+' | '+', '.join(j.get('display_claims',[]))+' | '+j['description']+' |')
 h+=[SEARCH,'</body></html>'];(R/'docs/index.html').write_text('\n'.join(h));(R/'docs/CALCULATIONS.md').write_text('\n'.join(md)+'\n')
 # A complete catalogue, not a list of opaque function names.
 cat=json.loads((R/'mathematica/checks_catalog.json').read_text());exp=json.loads((R/'mathematica/expected_checks.json').read_text());wl=(R/'mathematica/PentagonChecks.wl').read_text().splitlines()
 for k,v in cat.items():
  line=next((i+1 for i,x in enumerate(wl) if 'record["'+v['prefix']+'"' in x),None)
  if line:v['line']=line
 (R/'mathematica/checks_catalog.json').write_text(json.dumps(cat,indent=2,ensure_ascii=False)+'\n')
 wm=['# Wolfram check catalogue — manuscript v005','','Each record below states **what is tested, why, and how it relates to the paper**. The displayed paper reference identifies context; the logical role distinguishes a paper assertion from an auxiliary identity or finite diagnostic. All constants use circumradius-one normalization.','',
 '## Notation and scope','','`k=κ=cos(π/5)`, `s=σ=sin(π/5)`, `aK=a_crit`, `amin=1237/1000`, `epsN=aK-amin`, `epsM=1/125`. `triangleArea[a,b,c]` is Heron’s formula; `circleArea[a,b,r]` is the specified obtuse branch with short sides a,b and radius r. `positive[u]` means exact algebraic positivity, not a decimal tolerance.','',
 'Definitions and references are in `mathematica/PentagonChecks.wl`. The `condition` shown is the actual assertion template from that file; loop indices and selected side assignments are explained in each family. EXACT examples remain finite examples unless the assertion is symbolic or bounds a complete cell by a stated monotonicity argument. Numerical diagnostics use a fixed seed, 80 digits by default, and tolerance 10^-40.','',
 'To execute, follow [the package README](../mathematica/README.md). No OCaml run is triggered by this suite. The complete expected set is 161 IDs; a partial section run cannot supply a complete confirmation.','']
 wh=page('Wolfram paper-check catalogue — 161 assertions')
 wh+=['<p><a href="../mathematica/README.md">How to run in Mathematica or wolframscript</a> · <a href="index.html">Interval calculations</a>.</p><p>The exact constants use circumradius-one normalization. A paper reference locates context; the role states whether the check is an assertion from the paper, a supporting identity, an implementation fixture, or a numerical diagnostic. Numerical samples are not range proofs.</p><input id="search" aria-label="Search checks" placeholder="Search ID, lemma number, assertion or purpose">']
 for section in exp['sections']:
  wm+=['## '+section+' ('+str(len(exp['by_section'][section]))+' checks)',''];wh+=['<h2>'+E(section)+'</h2>']
  for k in exp['by_section'][section]:
   v=cat[k];ref=v['paper_reference']+' ['+v['label']+']';loc='mathematica/PentagonChecks.wl:'+str(v['line'])
   wm+=['### `'+k+'` — '+v['title'],'',f"**Role:** {v['role']}. **Method:** {v['kind']}. **Paper:** {ref}.",'','**Assertion:** '+v['assertion'],'','**Why:** '+v['why'],'','**Scope:** '+v['scope'],'','**Source:** `'+loc+'`; navigation code `'+v['comment_id']+'`.','', '```wolfram',v['condition'],'```','']
   wh.append('<article id="'+E(k)+'" data-search="'+E(k+' '+v['title']+' '+v['assertion']+' '+ref+' '+v['why'])+'"><h3>'+E(v['title'])+'</h3><p><code>'+E(k)+'</code></p><p><span class="tag">'+E(v['role'])+'</span><span class="tag">'+E(v['kind'])+'</span> '+E(ref)+'</p><p><strong>Assertion:</strong> '+E(v['assertion'])+'</p><p><strong>Why:</strong> '+E(v['why'])+'</p><p><strong>Scope:</strong> '+E(v['scope'])+'</p><details><summary>Exact expression and source</summary><p><a href="../mathematica/PentagonChecks.wl">'+E(loc)+'</a> · '+E(v['comment_id'])+'</p><pre>'+E(v['condition'])+'</pre></details></article>')
 wh += [SEARCH,'</body></html>'];(R/'docs/WOLFRAM_CHECKS.md').write_text('\n'.join(wm));(R/'docs/wolfram_checks.html').write_text('\n'.join(wh))
 print('Generated mathematical job and Wolfram catalogues.')
if __name__=='__main__':main()
