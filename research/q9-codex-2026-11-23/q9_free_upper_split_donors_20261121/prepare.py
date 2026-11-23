from pathlib import Path
from itertools import combinations
import json,random,sys
D=Path(__file__).resolve().parent;R=D.parent
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def canonical(w):
    def norm(s):
        m={};return ''.join(str(m.setdefault(c,len(m))) for c in s)
    return min(norm(w),norm(w[::-1]))
def valid(p):return len(set(p))==len(p) and all((x^y).bit_count()==1 for x,y in zip(p,p[1:])) and not any((x^y).bit_count()==1 for i,x in enumerate(p) for y in p[i+2:])
def word(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def go():
    rng=random.Random(863012);ws=(R/'q8_catalogue_96_98.words').read_text().split();seen=set()
    cases=[]
    for row,w in enumerate(ws):
        p=path(w);assert valid(p) and max(p)<256
        if len(w)==98:continue # the existing 98-edge branch explicitly studied one and two holes
        pairs=[(i,j) for i in range(5,len(p)-5) for j in range(i+12,len(p)-5) if (p[i]^p[j]).bit_count() in (2,3)]
        focus=rng.choice(pairs)
        # Two disjoint deleted bends leave three lower islands. Also include one-gap controls for the 97-edge parents.
        for holes in ([focus,(rng.randrange(6,len(p)-6),)] if len(w)==97 else [focus]):
            lower=[v for i,v in enumerate(p) if i not in holes]
            mask=sum(1<<v for v in lower)
            if mask in seen:continue
            seen.add(mask);cases.append(dict(id=len(cases),row=row,edges=len(w),holes=list(holes),lower=lower))
    (D/'cases.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in cases))
    control=[];original=json.loads((R/'q9_five_host_external_blocks_20261121/nine_witnesses.json').read_text())
    for r in original:
        if r['layer_crossings']!=2:continue
        p=r['vertices'];lo=sorted(x for x in p if x<256);hi=sorted(x-256 for x in p if x>=256)
        if len(lo)!=96:continue
        if any(g['ref']==r['reference'] for g in control):continue
        control.append(dict(ref=r['reference'],row=r['host'],lower=lo,upper_hint=hi,vertices=p))
    assert len(control)==5
    (D/'controls.json').write_text(json.dumps(control));print('cases',len(cases),'donor_rows',len({r['row'] for r in cases}),'controls',len(control))
if __name__=='__main__':go()

