"""Compare one, two three or four allowed external vertices against independent Q9 DFS."""
from collections import Counter
import json,random,subprocess,sys
from verify_q9_center_avoidance import verify
extra=int(sys.argv[2]) if len(sys.argv)>2 else 1
assert extra in (1,2,3,4)
rng=random.Random(94020)
def arm(dim):
    p=[rng.randrange(1<<dim)]
    while True:
        nexts=[p[-1]^(1<<d) for d in range(dim)]
        nexts=[z for z in nexts if z not in p and all((z^v).bit_count()!=1 for v in p[:-1])]
        if not nexts:return p
        p.append(rng.choice(nexts))

def oracle(host):
    universe=set(host)
    for _ in range(extra):universe |= {x^(1<<d) for x in universe for d in range(9)}
    best=[0]*(extra+1)
    def dfs(p,used,outside):
        best[outside]=max(best[outside],len(p)-1)
        v=p[-1]
        for d in range(9):
            x=v^(1<<d)
            if x in used or x not in universe or outside+int(x not in host)>extra:continue
            if any((u^x).bit_count()==1 for u in p[:-1]):continue
            dfs(p+[x],used|{x},outside+int(x not in host))
    for x in universe:dfs([x],{x},int(x not in host))
    return best

rows=[];cases=[];gain=Counter()
for i in range(4 if extra==4 else 12 if extra==3 else 72):
    dim=3+i%2;a=arm(dim);b=arm(dim);host=set(a)|{v+256 for v in b}
    results=oracle(host);best=max(results);gain[best-max(results[:-1])]+=1
    for target in (best,best+1):
        rows.append(" ".join(map(str,[target,len(a),len(b),*a,*b])))
        cases.append((best,target,host))
results=subprocess.run([sys.argv[1],{1:"--fixed-extra",2:"--fixed-two",3:"--fixed-three",4:"--fixed-four"}[extra]],input="\n".join(rows)+"\n",
                       text=True,capture_output=True,check=True).stdout.splitlines()
assert len(results)==len(cases)
for row,(best,target,host) in zip(results,cases):
    data=row.split();assert (data[0]=="FOUND")==(target<=best)
    if data[0]=="FOUND":
        p=list(map(int,data[1:]));verify(p);assert len(p)==target+1 and len(set(p)-host)<=extra
print(json.dumps(dict(domains=len(cases)//2,decisions=len(cases),gain_counts=gain)))
