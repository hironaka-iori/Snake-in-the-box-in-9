from pathlib import Path
from itertools import permutations
import hashlib,json
from collections import Counter
here=Path(__file__).resolve().parent
root=here.parent
def vertices(word):
    x=0;p=[x]
    for d in word:
        x^=1<<int(d);p.append(x)
    return p
def valid(p):
    return all(0<=x<256 for x in p) and len(set(p))==len(p) and all(((v^p[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j in range(i+1,len(p)))
def witness(file):
    vals=(here/file).read_text().splitlines()[0].split()
    p=list(map(int,vals[2:]));assert vals[0]=='WIT' and int(vals[1])==len(p) and valid(p)
    order=[v//32 for i,v in enumerate(p) if i==0 or p[i-1]//32!=v//32]
    assert order==[0,1,3,7,5,4,6,2]
    return dict(vertices=len(p),edges=len(p)-1,pairs=len(p)*(len(p)-1)//2,order=order,path=p)
def canon(w):
    return min(tuple(p[d] for d in x) for x in (w,w[::-1]) for p in permutations(range(3)))
def paths(x,seen,w):
    if len(w)==7:yield w
    for d in range(3):
        v=x^(1<<d)
        if v not in seen:yield from paths(v,seen|{v},w+(d,))
orbits=Counter(canon(w) for w in paths(0,{0},()))
assert len(orbits)==3
banks=[]
for fn in ['q7_q5_direct_47plus.words','q7_four_q5_47plus.words']:
    data=(root/fn).read_text().splitlines()
    for w in data:
        assert [c for c in w if c in '56']==list('565') and valid(vertices(w))
    assert len(set(data))==47076
    banks.append(set(data))
assert banks[0]==banks[1]
summary=dict(q3_orbits={''.join(map(str,k)):v for k,v in sorted(orbits.items())},bank_counts=dict(sorted(Counter(len(w)+1 for w in banks[0]).items())),witnesses={f:witness(f) for f in ['high95.log','positive.log','reversepositive.log']},logs={f:(here/f).read_text().splitlines()[-1] for f in ['97high.log','reverse97.log','high96.log','outer50target96.log','board96inner.log','board96outer.log']})
print(json.dumps(summary,indent=2))
