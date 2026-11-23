from pathlib import Path
from collections import Counter,defaultdict
import random,subprocess
D=Path(__file__).resolve().parent
def mask(vertices):return sum(1<<v for v in vertices)
def valid(p):return len(set(p))==len(p) and all(((v^w).bit_count()==1)==(j==i+1) for j,v in enumerate(p) for i,w in enumerate(p[:j]))
def verify_small():
    rng=random.Random(670253);catalog=defaultdict(set)
    def dfs(path):
        catalog[len(path)-1].add(mask(path))
        for axis in range(4):
            u=path[-1]^(1<<axis)
            if u not in path and all((u^x).bit_count()!=1 for x in path[:-1]):dfs(path+[u])
    for x in range(16):dfs([x])
    total=Counter()
    for target in range(3,9):
        for k in range(6):
            examples=[];expected=[]
            for _ in range(75):
                size=rng.randint(max(k+1,target-2),min(15,target+1+k))
                vertices=rng.sample(range(16),size);M=mask(vertices);examples.append(vertices)
                expected.append(any((M&~S).bit_count()==k for S in catalog[target]))
            data=''.join(' '.join(map(str,v))+'\n' for v in examples)
            result=subprocess.run([str(D/'search'),'4',str(target),str(k)],input=data,text=True,capture_output=True,check=True)
            rows=[list(map(int,l.split())) for l in result.stdout.splitlines()]
            assert len(rows)==len(expected)
            for q,exp,p in zip(rows,expected,examples):
                assert bool(q[1])==exp,(p,k,target,q,exp)
                if exp:assert valid(q[6:]) and len(q[6:])==target+1 and len(set(p)-set(q[6:]))==k
                total[exp]+=1
    print('exhaustive Q4 reference',dict(total))
def planted():
    rng=random.Random(671146);src=D.parent/'q9_group_walk/control.log'
    paths=[list(map(int,l.split()[9:])) for l in src.read_text().splitlines()[:16]]
    for k in range(1,5):
        seeds=[]
        for p in paths:
            H=set(p);kept=H-set(rng.sample(sorted(H),k));extra=rng.sample(sorted(set(range(512))-H),k)
            seeds.append(sorted(kept|set(extra)))
        data=''.join(' '.join(map(str,p))+'\n' for p in seeds)
        run=subprocess.run([str(D/'search'),'9','191',str(k)],input=data,text=True,capture_output=True,check=True)
        rows=[list(map(int,l.split())) for l in run.stdout.splitlines()];assert len(rows)==16
        for row,p in zip(rows,seeds):
            q=row[6:];assert row[1] and len(q)==192 and valid(q) and len(set(p)-set(q))==k
    print('planted Q9, 64 of 64 recovered 191 edges')
if __name__=='__main__':verify_small();planted()
