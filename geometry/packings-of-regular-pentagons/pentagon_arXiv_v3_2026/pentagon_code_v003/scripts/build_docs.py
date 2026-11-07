#!/usr/bin/env python3
"""Refresh code anchors, numbered paper references and index; optionally compile PDFs.
No mathematical source or author passage is rewritten. Run from any directory.
The supplied cached bibliography permits a build without BibTeX; regenerate it in
an ordinary TeX installation after changing bibliography contents.
"""
from pathlib import Path
import argparse,json,re,subprocess,sys,shutil
ROOT=Path(__file__).resolve().parents[1]

def source_map():
    out={}
    for p in sorted((ROOT/'ocaml').glob('*.ml')):
        text=p.read_text(); lines=text.splitlines()
        for m in re.finditer(r'^\s*let(?: rec)? ([a-zA-Z_][\w\']*)(?=\s|\(|=|:|$)',text,re.M):
            # A navigation anchor, not an OCaml parser or proof of scope.
            name=m[1];a=text[:m.start()].count('\n')+1
            while a<=len(lines) and not lines[a-1].strip():a+=1
            end=text.find(';;',m.end())
            b=text[:end+2].count('\n')+1 if end>=0 else a
            key=p.name+':'+name
            if key not in out:out[key]={'file':str(p.relative_to(ROOT)),'function':name,'start':a,'end':b}
    (ROOT/'docs/source-map.json').write_text(json.dumps(out,indent=2)+'\n')
    return out

def labels():
    p=ROOT/'paper/header_v005.aux'
    if not p.exists():return json.loads((ROOT/'paper/label-map.json').read_text())
    result={m[1]:{'number':m[2],'page':m[3]}for m in re.finditer(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{([^}]+)\}',p.read_text())}
    if len(result)<100:raise RuntimeError('Incomplete compiled label file; refusing to overwrite label map')
    (ROOT/'paper/label-map.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def refresh_commentary(labs):
    macro_labels={'PaperPseudoOne':'calc:pseudo1','PaperPseudoTwo':'calc:pseudo2','PaperPseudoArea':'calc:pseudo-area','PaperPseudoThree':'calc:pseudo-area3','PaperIsosceles':'calc:dimer-isosc','PaperThree':'calc:pent3','PaperFour':'calc:pent4','PaperLarge':'calc:large','PaperContactCoordinates':'sec:xalpha'}
    (ROOT/'docs/paperrefs.tex').write_text('% Generated from the compiled manuscript label map.\n'+''.join('\\newcommand{\\'+m+'}{'+labs[k]['number']+'}\n'for m,k in macro_labels.items()))
    template=(ROOT/'docs/code_commentary_template.txt').read_text()
    def snippet(m):
        fn,name,count=m.groups();lines=(ROOT/'ocaml'/fn).read_text().splitlines()
        a=next(i+1 for i,x in enumerate(lines)if re.match(r'\s*let(?: rec)? '+re.escape(name)+r'(?=\s|\(|=|$)',x))
        b=min(len(lines),a+int(count)-1)
        return '\\lstinputlisting[firstline='+str(a)+',lastline='+str(b)+',firstnumber='+str(a)+',caption={\\code{ocaml/'+fn+'}: \\code{'+name+'}}]{../ocaml/'+fn+'}'
    (ROOT/'docs/code_commentary.tex').write_text(re.sub(r'@@CODE (\S+) (\S+) (\d+)@@',snippet,template))
    entries=json.loads((ROOT/'docs/claims.json').read_text())
    for e in entries:
        if e.get('label') in labs:e['number']=labs[e['label']]['number']
    (ROOT/'docs/claims.json').write_text(json.dumps(entries,indent=2)+'\n')

def compile_tex(folder,name,passes=3):
    for _ in range(passes):
        p=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',name+'.tex'],cwd=ROOT/folder,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if p.returncode:
            sys.stderr.write(p.stdout.decode(errors='replace')[-8000:]);raise RuntimeError('TeX build failed: '+name)
    log=(ROOT/folder/(name+'.log')).read_text(errors='replace')
    if 'There were undefined references' in log or 'There were undefined citations' in log or 'multiply-defined labels' in log:raise RuntimeError('Unresolved references in '+name)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--compile',action='store_true');ap.add_argument('--figures',action='store_true');a=ap.parse_args()
    if a.compile:
        compile_tex('paper','header_v005')
        shutil.copyfile(ROOT/'paper/header_v005.pdf', ROOT/'paper/pentagon_v005.pdf')
    source_map();labs=labels();refresh_commentary(labs)
    subprocess.run([sys.executable,str(ROOT/'scripts/build_index.py')],check=True)
    if a.compile:compile_tex('docs','code_commentary')
    if a.figures:compile_tex('figures','gallery',3)
    print('Updated source map, paper references, commentary and index. Mathematical source unchanged.')
if __name__=='__main__':main()
