"""SAT completion for the full ordered walk of three coordinate groups."""
from itertools import combinations
from pathlib import Path
import sys,random,json
from pysat.solvers import Cadical195
D=Path(__file__).resolve().parent
def violations(p):
    return [(i,j) for j,b in enumerate(p) for i,a in enumerate(p[:j]) if a==b or (((a^b).bit_count()==1)!=(j==i+1))]
def lift(p,groups,budget,rng):
    bits=[[1<<d for d in g] for g in groups]
    masks=[sum(bs) for bs in bits]
    project=lambda x,k:sum(1<<j for j,b in enumerate(bits[k]) if x&b)
    colors=[];parity=[];ids=[];trajectory=[]
    for t,v in enumerate(p):
        if t==0:
            cell=[]
            for k in range(3):
                x=project(v,k);cell.append(len(colors));colors.append(min(x,7^x));parity.append(x.bit_count()%2)
        else:
            delta=v^p[t-1]
            idx=[k for k,m in enumerate(masks) if delta&m]
            if len(idx)!=1 or delta.bit_count()%2==0:return 'INCOMPATIBLE',0,0,None
            k=idx[0];x=project(v,k);cell=cell.copy();cell[k]=len(colors);colors.append(min(x,7^x));parity.append(x.bit_count()%2);trajectory.append(k)
        ids.append(cell)
    def literal(a,k):return 4*a+k+1
    fresh=4*len(colors)
    equal={}
    with Cadical195() as sat:
        for i in range(len(colors)):
            xs=[literal(i,c) for c in range(4)];sat.add_clause(xs)
            for a,b in combinations(xs,2):sat.add_clause([-a,-b])
        def eq(a,b):
            nonlocal fresh
            assert a!=b
            key=(min(a,b),max(a,b))
            if key not in equal:
                fresh+=1;e=equal[key]=fresh
                for c in range(4):
                    u,v=literal(a,c),literal(b,c)
                    sat.add_clause([-u,-v,e]);sat.add_clause([-e,-u,v])
            return equal[key]
        # Each group has the full four-color permutation symmetry.
        for a in ids[0]:sat.add_clause([literal(a,colors[a])])
        for t,k in enumerate(trajectory):sat.add_clause([-eq(ids[t][k],ids[t+1][k])])
        for j,b in enumerate(ids):
            for i in range(j-1):
                a=ids[i];odd=[k for k in range(3) if parity[a[k]]!=parity[b[k]]]
                if len(odd)>1:continue
                clause=[-eq(u,v) for k,(u,v) in enumerate(zip(a,b)) if u!=v and k not in odd]
                if odd:clause.append(eq(a[odd[0]],b[odd[0]]))
                sat.add_clause(clause)
        sat.set_phases([literal(i,c) for i,c in enumerate(colors)])
        bad=violations(p);free={u for i,j in bad for t in (i,j) for u in ids[t]}
        fixed={literal(i,c) for i,c in enumerate(colors) if i not in free}
        for iteration in range(256):
            remain=budget-sat.accum_stats()['conflicts']
            if remain<=0:return 'LIMIT',iteration,len(fixed),None
            sat.conf_budget(remain);ok=sat.solve_limited(assumptions=sorted(fixed))
            if ok is None:return 'LIMIT',iteration,len(fixed),None
            if ok:
                model=set(sat.get_model());q=[]
                for row in ids:
                    v=0
                    for k,a in enumerate(row):
                        c=next(h for h in range(4) if literal(a,h) in model)
                        x=c if c.bit_count()%2==parity[a] else 7^c
                        v+=sum(bb for h,bb in enumerate(bits[k]) if x&(1<<h))
                    q.append(v)
                assert not violations(q)
                return 'FOUND',iteration,len(fixed),q
            core=sat.get_core() or []
            if not core:return 'UNSAT',iteration,0,None
            if iteration>=18:fixed.clear()
            else:fixed.difference_update(rng.sample(sorted(core),min(8,len(core))))
        return 'LIMIT',256,len(fixed),None
def main():
    kind,count,seed,cap=sys.argv[1:];rng=random.Random(int(seed));count=int(count);cap=int(cap)
    if kind=='control':
        pool=[list(map(int,line.split()[9:])) for line in (D/'control.log').read_text().splitlines()]
    else:
        pool=[]
        for line in (D/'seam_rows.in').read_text().splitlines():
            pool.append(list(map(int,line.split())))
    for i in range(count):
        p=rng.choice(pool);ds=list(range(9));rng.shuffle(ds);gs=[ds[:3],ds[3:6],ds[6:]]
        s,it,n,q=lift(p,gs,cap,rng)
        print(json.dumps(dict(case=i,status=s,groups=gs,iterations=it,remaining_assumptions=n,vertices=q),separators=(',',':')),flush=True)
        if q and len(q)>=193:return
if __name__=='__main__':main()
