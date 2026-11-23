from pathlib import Path
from itertools import combinations
import json
D=Path(__file__).resolve().parent
def canon(w):
    def norm(o):
        m={};return ''.join(str(m.setdefault(k,len(m))) for k in o)
    return min(norm(w),norm(w[::-1]))
refs=Path('q9_three_axis_191.in').read_text().splitlines();ref={canon(w):i for i,w in enumerate(refs)}
hosts=[list(map(int,l.split())) for l in Path('q8_all_191_positive.hosts').read_text().splitlines()]
results=[];classes=set()
for i,vs in enumerate(hosts):
    S=set(vs);adj={x:{x^1<<k for k in range(9)}&S for x in S};stars=[{x,*z} for x,c in adj.items() for z in combinations(c,3)]
    labels=set()
    for a,b in combinations(vs,2):
        remove={a,b}
        if any(star.isdisjoint(remove) for star in stars):continue
        remaining=S-remove
        ends=[v for v in remaining if len(adj[v]-remove)==1]
        if len(ends)!=2:continue
        p=[ends[0]];rest=remaining-{ends[0]}
        for x in p:
            new=adj[x]&rest
            if not new:break
            assert len(new)==1;y,=new;rest.remove(y);p.append(y)
        if len(p)!=192:continue
        assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p) if i<j)
        w=''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]));r=ref[canon(w)];labels.add(r);classes.add(r)
        results.append(dict(host=i,reference=r,vertices=p,layer_crossings=w.count('8')))
    print('HOST',i,'191 reference rows',sorted(labels),'all included in whole-host domain search')
print('UNION',sorted(classes))
assert sorted(classes)==[27,32,37,39,57,62,96,103,128,129]
(D/'nine_witnesses.json').write_text(json.dumps(results))

