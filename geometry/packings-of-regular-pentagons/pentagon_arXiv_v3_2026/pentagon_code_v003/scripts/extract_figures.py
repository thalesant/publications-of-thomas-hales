#!/usr/bin/env python3
"""Extract original-style active TikZ calls from the shipped manuscript.
No TeX evaluation and no manuscript edit. Exact call contents are retained.
Gallery includes are refreshed, using the compiled paper label map.
"""
from pathlib import Path
import argparse,re,json,hashlib
ROOT=Path(__file__).resolve().parents[1]

def extract(text):
    def group(i):
        while i<len(text):
            if text[i].isspace():i+=1;continue
            if text[i]=='%':i=text.index('\n',i)+1;continue
            break
        if i==len(text) or text[i]!='{':raise ValueError('Missing TeX argument')
        start=i;depth=0
        while i<len(text):
            if text[i]=='%'and(i==0 or text[i-1]!='\\'):
                i=text.index('\n',i);continue
            if text[i]=='{'and(i==0 or text[i-1]!='\\'):depth+=1
            if text[i]=='}'and(i==0 or text[i-1]!='\\'):
                depth-=1
                if not depth:return text[start:i+1],i+1
            i+=1
        raise ValueError('Unclosed TeX argument')
    result=[]
    for m in re.finditer(r'^\\tikzfig(?=\{)',text,re.M):
        i=m.end();args=[]
        for _ in range(3):g,i=group(i);args.append(g)
        result.append((args[0][1:-1],args[1][1:-1],text[m.start():i],text[:m.start()].count('\n')+1))
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--manuscript',type=Path,default=ROOT/'paper/pentagon_v005.tex');a=ap.parse_args()
    text=a.manuscript.read_text();items=extract(text);labels=json.loads((ROOT/'paper/label-map.json').read_text());seen=set();manifest=[]
    for label,caption,body,line in items:
        key='fig:'+label
        if key in seen:raise RuntimeError('Duplicate figure label: '+key)
        seen.add(key);num=labels[key]['number'];fn='figure_'+re.sub('[^a-zA-Z0-9_-]','_',label)+'.tex'
        (ROOT/'figures'/fn).write_text('% Exact TikZ call from '+a.manuscript.name+'; no geometric modification.\n'+body+'\n')
        manifest.append(dict(label=key,number=num,source_file=a.manuscript.name,source_line=line,file=fn,sha256=hashlib.sha256(body.encode()).hexdigest(),caption=caption))
    if not manifest:raise RuntimeError('No figures found; refusing an empty extraction')
    (ROOT/'figures/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    # The gallery preamble/reference map is a preserved build input; refresh just the include body.
    gp=ROOT/'figures/gallery.tex';g=gp.read_text();start=g.index('\\def\\currentfigurenumber')
    body=''.join('\\def\\currentfigurenumber{'+e['number']+'}\n\\input{'+e['file']+'}\n\\clearpage\n'for e in manifest)
    gp.write_text(g[:start]+body+'\\bibliographystyle{plainnat}\n\\bibliography{../paper/pentagon}\n\\end{document}\n')
    print('Extracted',len(manifest),'figures. Original manuscript unchanged.')
if __name__=='__main__':main()
