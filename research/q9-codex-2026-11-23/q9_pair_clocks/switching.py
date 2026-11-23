from pathlib import Path
from pysat.solvers import Cadical195
from search import axes,validate,D
import random,subprocess,json,sys
from collections import Counter
def solve(w,alt,cap,refs=None):
    lines=subprocess.check_output([D/'switching',''.join(map(str,w)),''.join(map(str,alt))],text=True).splitlines()
    sel=list(map(int,lines[0].split()[2:]));clauses=[list(map(int,l.split()[:-1])) for l in lines[2:]]
    with Cadical195(bootstrap_with=clauses) as solver:
        if refs is not None:solver.set_phases([v if a==c else -v for v,a,c in zip(sel,w,refs)])
        solver.conf_budget(cap);r=solver.solve_limited();k=solver.accum_stats()['conflicts']
        if r!=True:return ('UNSAT' if r is False else 'UNKNOWN'),None,k
        model=set(solver.get_model());p=axes([a if v in model else b for v,a,b in zip(sel,w,alt)])
        assert len(p)==len(w)+1 and validate(p);return 'FOUND',p,k
def run(n,trials,seed,quota):
    rng=random.Random(seed)
    raw=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    moms=[list(map(int,w)) for w in (D.parent/'q9_gap_generations/prior191.words').read_text().split()]
    def matching():
        ds=list(range(9));rng.shuffle(ds);return {ds[i]:ds[i^1] if i<8 else ds[i] for i in range(9)}
    stats=Counter()
    for job in range(trials):
        if job%3==0:
            w=rng.choice(moms).copy()
            while len(w)<n:w.insert(rng.randrange(len(w)+1),rng.randrange(9))
        else:w=rng.choice(raw).copy()
        p=axes(w);contacts=[(i,j) for j,v in enumerate(p) for i,u in enumerate(p[:max(0,j-1)]) if (v^u).bit_count()<2]
        if not contacts:assert validate(p);print(json.dumps(dict(witness=p)),flush=True);return
        i,j=rng.choice(contacts);c=rng.choice([i,j]);m=matching();m2=matching()
        width=rng.choice([4,9,18,32,54,72,96]);start=max(0,c-rng.randrange(width));stop=min(n,start+width)
        alt=[(m2 if start<=t<stop else m)[a] for t,a in enumerate(w)]
        st,v,k=solve(w,alt,quota,w);stats[st]+=1
        if v:
            print(json.dumps(dict(witness=v,original=w,alternative=alt,status=st,job=job)),flush=True);break
        if job%25==24:print(json.dumps(dict(tested=job+1,counts=stats)),flush=True)
    print(json.dumps(dict(done=True,counts=stats)),flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
