"""Change an entire block-parity lift while temporarily admitting the donor's single chord."""
import json,random,sys,time
from collections import Counter
from pathlib import Path
from pysat.solvers import Solver
from lift_q9_by_block_parities import build
from repair_q9_time_projection import valid

def key(p):
    words=[(v^w).bit_length()-1 for v,w in zip(p,p[1:])]
    def root(seq):
        axes={}
        return bytes(axes.setdefault(x,len(axes)) for x in seq)
    return min(root(words),root(reversed(words)))

def flaws(p):
    return [(i,j) for j,y in enumerate(p) for i in range(j-1) if (y^p[i]).bit_count()<2]

def endpoint_extensions(p):
    for s in (p,p[::-1]):
        for k in range(9):
            q=s+[s[-1]^1<<k]
            if valid(q):return q

def candidates(p,g,r,free,budget,exception):
    inst=build(p,g,r,free,exception)
    if inst is None:return
    clauses,hints,rows,parities,tables=inst
    if not hints:return
    clauses.append([-x for x in hints])
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        solver.set_phases(hints)
        for _ in range(5 if exception else 1):
            solver.conf_budget(budget)
            if solver.solve_limited() is not True:return
            model=set(solver.get_model());out=[]
            for row,par in zip(rows,parities):
                x=0
                for j,v in enumerate(row):
                    m=v if type(v) is int else next(i for i,b in enumerate(v) if b in model)
                    x|=tables[j][(par>>j)&1,m]
                out.append(x)
            yield out
            chosen={next(b for b in v if b in model) for row in rows for v in row if type(v) is tuple}
            solver.add_clause([-b for b in chosen])

def main():
    src,ref,mins,seed=sys.argv[1:5];r=random.Random(int(seed))
    known={key(list(map(int,l.split()))) for l in Path(ref).read_text().splitlines() if l}
    assert len(known)==131
    bank=[];seen=set()
    for l in Path(src).read_text().splitlines():
        p=list(map(int,l.split()))
        if any((x^y).bit_count()!=1 for x,y in zip(p,p[1:])) or len(p)!=193 or len(set(p))!=193:raise ValueError('seed')
        # Linear-time chord counting via the inverse maps of occupied vertices.
        ix={v:i for i,v in enumerate(p)}
        bad=[(i,j) for i,v in enumerate(p) for b in range(9) if (j:=ix.get(v^(1<<b),-1))>i+1]
        assert len(bad)==1
        k=key(p)
        if k not in seen:bank.append((p,bad[0]));seen.add(k)
    head=len(bank);start=time.monotonic();trials=0;stats=Counter();clock=start
    while time.monotonic()<start+float(mins)*60:
        trials+=1
        n=r.randrange(head,len(bank)) if len(bank)>head and r.randrange(5) else r.randrange(len(bank))
        p,chord=bank[n];axes=list(range(9));r.shuffle(axes);bins=r.choice([(3,3,3),(3,2,2,2),(3,3,2,1),(2,2,2,2,1)])
        groups=[]
        for b in bins:groups.append(axes[:b]);axes=axes[b:]
        tol=not len(bank)>head or r.random()<.68
        for q in candidates(p,groups,r,r.choice([.15,.23,.32,.45,.55,.7,.85]),r.choice([400,800,1600]),chord if tol else None):
            stats['solution']+=1
            if not tol or key(q) not in seen:
                bad=flaws(q)
                assert all((x^y).bit_count()==1 for x,y in zip(q,q[1:])) and len(set(q))==len(q)
                if not bad:
                    assert valid(q);print(json.dumps(['FOUND192',q]),flush=True);return
                assert tol and bad==[chord]
                k=key(q);seen.add(k);bank.append((q,chord));stats['new']+=1
                print(json.dumps(['ONE',n,chord,q],separators=(',',':')),flush=True)
                for j,seg in [(0,q[1:]),(192,q[:-1])]:
                    if j not in chord:continue
                    assert valid(seg);ck=key(seg)
                    if ck not in known:
                        print(json.dumps(['NEW191',seg]),flush=True);known.add(ck)
                        ext=endpoint_extensions(seg)
                        if ext:print(json.dumps(['FOUND192',ext]),flush=True);return
        if time.monotonic()>clock+75:
            print(json.dumps(['STATUS',trials,len(bank),dict(stats)]),flush=True);clock=time.monotonic()
    print(json.dumps(['DONE',trials,len(bank),dict(stats)]),flush=True)
if __name__=='__main__':main()
