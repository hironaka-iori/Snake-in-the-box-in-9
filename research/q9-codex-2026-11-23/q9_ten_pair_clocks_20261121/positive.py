from pathlib import Path
from collections import Counter
import json,random
D=Path(__file__).resolve().parent;R=D.parent
def walk(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def damage(p):
    flags=[0]*1024;e=0
    for i,v in enumerate(p):
        e+=flags[v]+sum(flags[v^1<<k] for k in range(10))-int(i>0);flags[v]+=1
    return e
def canonical(q):
    def f(v):
        m={};return tuple(m.setdefault(x,len(m)) for x in v)
    return min(f(q),f(q[::-1]))
def fold(q,a,b):
    dims=[k for k in range(10) if k!=b]
    return [dims.index(a if c==b else c) for c in q]
def main():
    rng=random.Random(591472);bank=(R/'q9_gap_generations/prior191.words').read_text().split();meta=[];samples=[];assert len(bank)==131
    for row in rng.sample(range(131),60):
        target=list(map(int,bank[row]));pm=rng.sample(range(9),9);ds=[pm[j:j+2] for j in range(0,8,2)]+[[pm[-1]]]
        gr={a:k for k,g in enumerate(ds) for a in g}
        base=[gr[a]*2+(ds[gr[a]].index(a) if gr[a]<4 else rng.randrange(2)) for a in target]
        assert not damage(walk(base));m=base[:];best=None;accepted=0
        for iter in range(430):
            b=rng.randrange(4);ix=[k for k,c in enumerate(m) if c//2==b]
            i=rng.randrange(len(ix));j=max(0,min(len(ix)-1,i+rng.randint(-8,8)))
            if i==j:continue
            t,s=ix[i],ix[j];m[t]^=1;m[s]^=1
            if damage(walk(m)):
                m[t]^=1;m[s]^=1;continue
            accepted+=1;w=fold(m,8,9);bad=damage(walk(w))
            if bad and (best is None or bad>best[0]):best=(bad,m[:],accepted)
            if best and best[0]>=3:break
        if not best:continue
        bad,m,ac=best;p=walk(m);assert not damage(p) and len(set(m))==10
        if any(not damage(walk(fold(m,a,b))) for a in range(10) for b in range(a+1,10)):continue
        samples.append(p);meta.append(dict(archive=row,raw_dim_groups=ds,base=base,source_steps=m,collapsed_defects=bad,accepted_edits=ac))
        if len(samples)==28:break
    (D/'controls.pts').write_text(''.join('10 '+' '.join(map(str,p))+'\n' for p in samples))
    (D/'controls.json').write_text(json.dumps(meta,separators=(',',':'))+'\n')
    with (D/'controls.tsv').open('w') as f:
        for i,r in enumerate(meta):
            w=[min(t,8) for t in r['source_steps']];print(i,0,-1,'0123456788',r['collapsed_defects'],''.join(str(x//2) for x in w),''.join(map(str,w)),file=f)
    print('true_191',len(samples),'all_45_constant_collapses_invalid',len(samples),'raw_defects',Counter(z['collapsed_defects'] for z in meta))
if __name__=='__main__':main()
