"""Fixed-basis independent completion model including every optional vertex."""
from pathlib import Path
from random import Random
from collections import Counter
from itertools import combinations
from pysat.solvers import Minicard
from subprocess import run
import json
D=Path(__file__).resolve().parent;R=D.parent
def solve(required,holes):
    s=set(required);n=len(s)+holes;nei=[[v^(1<<g) for g in range(9)] for v in range(512)];xs=[i+1 for i in range(512)]
    with Minicard() as z:
        opt=[v+1 for v in set(range(512))-s];z.add_atmost(opt,holes);z.add_atmost([-x for x in opt],len(opt)-holes)
        for v in s:z.add_clause([v+1])
        for v,N in enumerate(nei):
            # If v is selected, at least one and at most two neighbours may be selected.
            aff=[y+1 for y in N];z.add_clause([-(v+1)]+aff)
            if v in s:z.add_atmost(aff,2)
            else:
                for a,b,c in combinations(aff,3):z.add_clause([-(v+1),-a,-b,-c])
        while z.solve():
            vset={x-1 for x in z.get_model() if 1<=x<=512};assert s<=vset and len(vset)==n
            tips=[x for x in vset if len(set(nei[x])&vset)==1]
            if len(tips)==2:
                done=[];x=tips[0];prev=None
                while x is not None:
                    done.append(x);x,prev=next((y for y in nei[x] if y in vset and y!=prev),None),x
                if len(done)==n:return done
            z.add_clause([-(x+1) for x in vset-s])
    return None
def valid(p,s,h):
    assert len(p)==len(s)+h and len(set(p))==len(p) and s<=set(p)
    assert all(((x^p[j]).bit_count()==1)==(i+1==j) for i,x in enumerate(p) for j in range(i+1,len(p)))
def main():
    rng=Random(321689);bank=(R/'q9_gap_generations/prior191.words').read_text().split();tests=[]
    for i in range(70):
        w=bank[i];p=[0]
        for ch in w:p.append(p[-1]^1<<int(ch))
        h=i%5+1
        if i%3==0:gone=range(54,54+h)
        elif i%3==1:gone=rng.sample(range(2,189),h)
        else:gone=range(h)
        s={x for j,x in enumerate(p) if j not in gone}
        if i>=35:
            # Replace a retained point by an unrelated compulsory point. The resulting set is decided by both oracles.
            s.remove(rng.choice(sorted(s)));s.add(rng.choice(sorted(set(range(512))-set(p))))
        tests.append((s,h))
    raw=''.join(str(h)+' '+' '.join(map(str,sorted(s)))+'\n' for s,h in tests)
    output=run([str(D/'supplied_forest')],input=raw,text=True,capture_output=True,check=True).stdout.splitlines()
    stats=Counter()
    for i,((s,h),line) in enumerate(zip(tests,output)):
        j,r,*q=map(int,line.split());assert j==i
        p=solve(s,h);assert bool(p)==bool(r)
        if p:valid(p,s,h);valid(q,s,h)
        assert i>=35 or p
        print(json.dumps(dict(case=i,holes=h,agreed=bool(p),compulsory=sorted(s),physical_sat_path=p,supplied_path=q)),flush=True)
if __name__=='__main__':main()
