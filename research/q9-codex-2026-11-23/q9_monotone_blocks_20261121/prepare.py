from pathlib import Path
from itertools import combinations
import random,json
D=Path(__file__).resolve().parent;root=D.parent
def path(w):
    v=0;p=[v]
    for k in w:v^=1<<int(k);p.append(v)
    return p
def defects(p):
    assert len(p)==len(set(p))
    return [(i,j,(x^y).bit_length()-1) for j,y in enumerate(p) for i,x in enumerate(p[:j-1] if j else []) if (x^y).bit_count()==1]
def frame(x,a,b):
    bits=[i for i in range(9) if i not in (a,b)]
    return ((x>>a&1)+2*(x>>b&1),sum(((x>>k)&1)<<j for j,k in enumerate(bits)))
def put(g,v,a,b):
    bits=[i for i in range(9) if i not in (a,b)]
    return (g&1)<<a|(g>>1)<<b|sum((v>>j&1)<<k for j,k in enumerate(bits))
def go():
    blob=(root/'q9_via_q10/monotone_near.words').read_text().split()
    meta=[]
    with (D/'target.in').open('w') as out,(D/'ordered.in').open('w') as ordout:
        for i,w in enumerate(blob):
            if len(w)!=192:continue
            p=path(w);ch=defects(p)
            if len(ch)!=2:continue
            meta.append(dict(id=i,chords=ch))
            for a,b in combinations(range(9),2):
                print(i,a,b,*p,file=out)
                if {a,b}=={z[2] for z in ch}:print(i,a,b,*p,file=ordout)
    (D/'target.json').write_text(json.dumps(meta)+'\n')
    ar=(root/'q9_gap_generations/prior191.words').read_text().split();rn=random.Random(327855);meta=[]
    with (D/'control.in').open('w') as f,(D/'unmoved.in').open('w') as t:
        for i in rn.sample(range(len(ar)),24):
            p=path(ar[i]);a,b=rn.sample(range(9),2);a,b=sorted((a,b))
            # Reroute the block placements before the solver sees them.
            charts=[];layout=rn.sample(range(4),4)
            for k in range(4):charts.append((rn.sample(range(7),7),rn.randrange(128)))
            q=[]
            for x in p:
                g,u=frame(x,a,b);pm,off=charts[g];v=off^sum((u>>j&1)<<k for j,k in enumerate(pm));q.append(put(layout[g],v,a,b))
            assert len(q)==len(set(q));meta.append(dict(id=i,axes=[a,b],layout=layout,chart=charts))
            print(i,a,b,*q,file=f);print(i,a,b,*p,file=t)
    (D/'control.json').write_text(json.dumps(meta)+'\n')
if __name__=='__main__':go()
