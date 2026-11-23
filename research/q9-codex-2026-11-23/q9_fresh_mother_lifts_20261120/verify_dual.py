"""Independent integer-only upper check for two tip crossings at a fixed Q8 middle."""
from pathlib import Path
import json
import gzip
from itertools import combinations
import sys

def check(entry, *, compare_saved=True):
    w=entry['word'];p=[0]
    for d in w:p.append(p[-1]^(1<<int(d)))
    assert len(set(p))==len(p) and all(((x^y).bit_count()==1)==(i+1==j) for i,x in enumerate(p) for j,y in enumerate(p) if i<j)
    roots={p[0],p[-1]};outside=set(range(256))-set(p[1:-1]);ep=entry['outer_parity']
    c=entry['certificate'];masks=[sum(1<<d for d in ds) for ds in c['axes']]
    assert ep in (0,1) and len(set(masks))==len(masks) and all(len(ds)==3 and len(set(ds))==3 and all(type(d)==int and 0<=d<8 for d in ds) for ds in c['axes'])
    weight={(m,v,i):a for m,v,i,a in c['weights']}
    fee,balance,scale=(c[k] for k in ['end_weight','balance_weight','scale'])
    assert type(scale)==int and scale>0 and all(type(t)==int for t in (fee,balance,*weight.values()))
    numerator=2*fee+(len(p)%2+(1 if ep==0 else -1))*balance
    local={}
    for v in outside:
        dirs=[1<<k for k in range(8) if (v^(1<<k)) in outside]
        values=[] if v in roots else [0]
        allowed=[]
        for n in range(3):
            deg=n+int(v in roots)
            if deg!=2 and (deg!=1 or (v.bit_count()&1)!=ep):continue
            for ids in combinations(dirs,n):
                sig=sum(ids);allowed.append(sig)
                values.append(scale-balance*(1 if v.bit_count()%2==0 else -1)-fee*(deg==1)+sum(weight.get((m,v,sig&m),0) for m in masks))
        assert values;local[v]=allowed;numerator+=max(values)
    for mask in masks:
        directions=[1<<k for k in range(8) if mask>>k&1]
        for base in range(256):
            if base&mask:continue
            candidates=sorted(v for v in outside if v&~mask==base)
            if not candidates:continue
            needed=roots&set(candidates)
            signatures={v:{z&mask for z in local[v]} for v in candidates}
            best=None
            for subset in range(1<<len(candidates)):
                cells={v for k,v in enumerate(candidates) if subset>>k&1}
                if not needed<=cells:continue
                neighbors={v:[i for i in directions if (v^i) in cells] for v in cells}
                if any(sum(ids) not in signatures[v] for v,ids in neighbors.items()):continue
                # Every component of an induced forest must have strictly fewer edges than vertices.
                seen=set()
                for v in cells:
                    if v in seen:continue
                    todo=[v];verts=edges2=0
                    while todo:
                        x=todo.pop()
                        if x in seen:continue
                        seen.add(x);verts+=1;edges2+=len(neighbors[x]);todo.extend(x^i for i in neighbors[x])
                    if edges2>=2*verts:break
                else:
                    val=-sum(weight.get((mask,v,sum(ids)),0) for v,ids in neighbors.items())
                    best=val if best is None else max(best,val)
            assert best is not None
            numerator+=best
    if compare_saved:assert numerator==entry['bound']
    return numerator,scale,193-len(p)

if __name__=='__main__':
    good=both=seen=0;opts={}
    for filename in sys.argv[1:]:
        with gzip.open(filename,'rt') as inp:
            for line in inp:
                row=json.loads(line);b,s,t=check(row);seen+=1;opts.setdefault(row['word'],set())
                if b<t*s:
                    good+=1;opts[row['word']].add(row['outer_parity'])
    print(json.dumps(dict(checked=seen,excluded_colors=good,both_colors=sum(len(x)==2 for x in opts.values()))))
