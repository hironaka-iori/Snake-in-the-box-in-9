from itertools import permutations
from pathlib import Path
import hashlib
from math import factorial
base=Path(__file__).resolve().parent
source=Path("q9_reordered_segments_20261120/reference191.words")
def valid(p):
    return (len(set(p))==len(p) and all(0<=x<512 for x in p) and
            all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p) if i<j))
bank=[]
for line in source.read_text().splitlines():
    p=[0]
    for x in line:p.append(p[-1]^(1<<int(x)))
    assert len(p)==192 and valid(p)
    bank.append(p)
assert len(bank)==131
print("Validated 131 parents; input SHA256",hashlib.sha256(source.read_bytes()).hexdigest())
ctrl=(base/"control.log").read_text()
w=list(map(int,ctrl.split(" vertices ")[1].split()))
p=bank[0]
s=p[:2]+[x^7 for x in p[5:]]
assert len(s)==189 and valid(s) and len(w)==192 and valid(w)
print("Checked shortened control 188 edges and repaired control 191 edges via all unordered vertex pairs.")
samples=[]
for line in (base/"five_windows.log").read_text().splitlines():
    if line=='DONE':continue
    v=line.split()
    a,b,l,n,count=map(int,[v[1],v[2],v[4],v[6],v[8]])
    assert l==b-a+1
    before={x^k for x in p[:a+1] for k in [0]+[1<<i for i in range(9)]}
    shifts=[sh for sh in range(512) if (p[a]^p[b]^sh).bit_count()>=2 and (p[a]^p[b]^sh).bit_count()%2==l%2 and all((x^sh) not in before for x in p[b:])]
    assert len(shifts)==n
    nframes=0
    for t,sh in enumerate(shifts):
        d=(p[a]^p[b]^sh).bit_count()
        for k,q in enumerate(bank[1:]):
            for j in range(len(q)-l):
                if (q[j]^q[j+l]).bit_count()==d:
                    nframes+=2
                    if t==0 and not any(s[0]==a for s in samples):samples.append((a,b,sh,q[j:j+l+1]))
    assert nframes==count
    print("Window",a,b,"independently reproduced eligible shifts and oriented donor counts",n,count)
bit=[1<<i for i in range(9)]
for a,b,sh,seg in samples:
    d=seg[0]^seg[-1];goal=p[a]^p[b]^sh
    transformed=0
    for perm in permutations(bit):
        if sum(perm[k] for k in range(9) if d&bit[k])!=goal:continue
        transformed+=1
        middle=[p[a]^sum(perm[k] for k in range(9) if (x^seg[0])&bit[k]) for x in seg]
        w=p[:a]+middle+[x^sh for x in p[b+1:]]
        assert not valid(w)
    assert transformed==factorial(d.bit_count())*factorial(9-d.bit_count())
    print("Direct permutation audit for one eligible donor per window:",a,b,transformed,"failed anchor-compatible isometries")
for n in ("search","reverse"):
    r=(base/(n+".log")).read_text()
    assert r.startswith("DONE")
    print(n,r.strip())

