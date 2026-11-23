from itertools import combinations,permutations
from math import prod
from pathlib import Path
import subprocess,random,json
ref="q9_odd_reference_vertices.txt";bank=[list(map(int,l.split())) for l in open(ref)]
def valid(p):
    return len(set(p))==len(p) and all(0<=v<512 for v in p) and all(((v^p[k]).bit_count()==1)==(k==j+1) for j,v in enumerate(p) for k in range(j+1,len(p)))
assert all(len(p)==192 and valid(p) for p in bank)
assert all(not valid(q+[q[-1]^(1<<b)]) for p in bank for q in (p,p[::-1]) for b in range(9))
def expected(s):
    N={x:{x^(1<<j) for j in range(9)} for x in s}
    count={y:sum(y in n for n in N.values()) for y in set.union(*N.values())}
    ways=orders=0
    for seq in permutations(s):
        choices=[sum(count[y]==1 for y in N[seq[0]])]+[sum(count[y]==2 for y in N[a]&N[b]) for a,b in zip(seq,seq[1:])]
        m=prod(choices);ways+=m;orders+=bool(m)
    return orders,ways
rng=random.Random(31167);ev=[x for x in range(32) if x.bit_count()%2==0]
cases=list(combinations(ev[:8],4))+[rng.sample(ev,5) for _ in range(40)]
entries="".join(" ".join(map(str,t))+"\n" for t in cases)
out=subprocess.check_output(["/tmp/q9oddcheck21",ref,"100000","counts"],input=entries,text=True)
comp=[tuple(map(int,l.split()[1:])) for l in out.splitlines() if l.startswith("COUNT ")]
assert len(comp)==len(cases)
for t,res in zip(cases,comp):assert res==(*expected(t),0),(t,res,expected(t))
# Withhold one full class, supply just its parity set and recover the withheld path.
reduced=Path("/tmp/q9-oddorders-heldout-ref21.txt")
reduced.write_text(" ".join(map(str,bank[1]))+"\n")
c=subprocess.check_output(["/tmp/q9oddcheck21",str(reduced),"100000"],input=" ".join(map(str,bank[0][::2]))+"\n",text=True)
def key(p):
    def ks(p):
        m={};return tuple(m.setdefault(a^b,len(m)) for a,b in zip(p,p[1:]))
    return min(ks(p),ks(p[::-1]))
paths=[list(map(int,l.split()[1:])) for l in c.splitlines() if l.startswith("NOVEL191 ")]
assert paths and all(valid(p) for p in paths) and key(bank[0]) in {key(p) for p in paths}
print(json.dumps(dict(small_allorders=len(cases),positive_small=sum(k>0 for k,_,_ in comp),orientations=sum(k for k,_,_ in comp),lifts=sum(k for _,k,_ in comp),verified_reference=len(bank),tested_end_extensions=len(bank)*18,withheld_recovered=True)))
