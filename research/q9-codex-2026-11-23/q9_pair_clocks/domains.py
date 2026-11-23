from search import D,axes,validate
from pysat.solvers import Cadical195
from collections import Counter
import random,json,sys,subprocess
def solve(w,domains,quota):
    masks=[sum(1<<c for c in choices) for choices in domains]
    rows=subprocess.check_output([D/'domains',''.join(f'{m:03x}' for m in masks)],text=True).splitlines()
    ids=iter(map(int,rows[0].split()[2:]));choices=[[(d,next(ids)) for d in sorted(group)] for group in domains]
    cl=[list(map(int,row.split()[:-1])) for row in rows[2:]]
    with Cadical195(bootstrap_with=cl) as sol:
        sol.set_phases([v if d==a else -v for a,row in zip(w,choices) for d,v in row])
        sol.conf_budget(quota);r=sol.solve_limited();k=sol.accum_stats()['conflicts']
        if r!=True:return 'UNKNOWN' if r is None else 'UNSAT',None,k
        model=set(sol.get_model());z=[next(d for d,v in row if v in model) for row in choices];p=axes(z)
        assert len(p)==len(w)+1 and validate(p);return 'FOUND',p,k
def main(n,total,seed,quota):
    rng=random.Random(seed);raw=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    mothers=[list(map(int,w)) for w in (D.parent/'q9_gap_generations/prior191.words').read_text().split()]
    counts=Counter()
    for t in range(total):
        if t%4==0:
            w=rng.choice(mothers).copy()
            while len(w)<n:w.insert(rng.randrange(len(w)+1),rng.randrange(9))
        else:w=rng.choice(raw)
        p=axes(w);pairs=[(i,j) for j,v in enumerate(p) for i,u in enumerate(p[:max(j-1,0)]) if (v^u).bit_count()<2]
        if not pairs:assert validate(p);print(json.dumps(dict(found=p)),flush=True);break
        ds=list(range(9));rng.shuffle(ds);pair={ds[i]:ds[i^1] if i<8 else ds[i] for i in range(9)}
        domains=[{a,pair[a]} for a in w];cs=rng.sample(pairs,min(len(pairs),rng.randint(1,2)))
        for i,j in cs:
            center=rng.choice((i,j));radius=rng.choice([1,2,3,6]);extra=rng.sample(range(9),rng.choice([2,4,9]))
            for pos in range(max(0,center-radius),min(n,center+radius)):domains[pos].update(extra)
        st,v,k=solve(w,domains,quota);counts[st]+=1
        if v:print(json.dumps(dict(found=v,steps=n,job=t)),flush=True);break
        if t%20==19:print(json.dumps(dict(completed=t+1,counts=counts)),flush=True)
    print(json.dumps(dict(done=True,counts=counts)),flush=True)
if __name__=='__main__':main(*map(int,sys.argv[1:]))
