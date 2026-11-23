"""Exact lift of a time-ordered word over disjoint groups of coordinate axes."""
from collections import defaultdict,Counter
from itertools import combinations
from search import D,validate,axes
from pathlib import Path
import json,random,sys
from pysat.solvers import Cadical195
def run(w,groups,cap,lock=0,rng=None):
    lookup={a:i for i,g in enumerate(groups) for a in g};d=len(groups);n=0
    cnf=[];xors={};warm=[];state=[];trace=[];bucket=defaultdict(list);phase=0;v=0;first=set();one=None
    for group in groups:
        row=tuple(range(n+1,n+len(group)));n+=len(row);cnf.extend([[-x] for x in row]);state.append(row)
    def xor(a,b):
        nonlocal n
        if a==b:return None
        key=(min(a,b),max(a,b))
        if key not in xors:
            n+=1;z=n;xors[key]=z
            cnf.extend(([-z,a,b],[-z,-a,-b],[z,a,-b],[z,-a,b]))
        return xors[key]
    for t in range(len(w)+1):
        if t:
            a=w[t-1];k=lookup[a];g=groups[k];prev=state[k];v^=1<<a;phase^=1<<k
            now=tuple(range(n+1,n+len(g)));n+=len(now);state[k]=now
            vals=[x if v&(1<<b) else -x for x,b in zip(now,g[:-1])];warm+=vals
            if k not in first:cnf.extend([[x] for x in vals]);first.add(k)
            elif lock:
                for lit in vals:
                    if rng.random()<lock:cnf.append([lit])
            flips=[xor(a,b) for a,b in zip(now,prev)]
            cnf.extend([[-a,-b] for a,b in combinations(flips,2)])
        trace.append(tuple(state));bucket[phase].append(t)
    requests=set()
    for key,ts in bucket.items():
        for k in range(-1,d):
            other=key if k<0 else key^(1<<k)
            if other<key or other not in bucket:continue
            for i in ts:
                for j in bucket[other]:
                    if abs(i-j)<=1 or (key==other and i>j):continue
                    outside=[];inner=[]
                    for h,(u,v) in enumerate(zip(trace[i],trace[j])):
                        if u!=v:
                            target=inner if k==h else outside
                            target.extend(xor(a,b) for a,b in zip(u,v))
                    tests=[outside] if len(inner)<2 else [outside+inner[:h]+inner[h+1:] for h in range(len(inner))]
                    for cl in tests:
                        if not cl:return 'UNSAT',None,0
                        requests.add(tuple(sorted(cl)))
    cnf.extend(requests)
    with Cadical195(bootstrap_with=cnf) as sol:
        sol.set_phases(warm);sol.conf_budget(cap);z=sol.solve_limited();spent=sol.accum_stats()['conflicts']
        if z!=True:return ('UNSAT' if z is False else 'UNKNOWN'),None,spent
        model=set(sol.get_model());rec=[]
        for t,c in enumerate(w):
            k=lookup[c];g=groups[k];selected=[a for a,b,d in zip(g,trace[t][k],trace[t+1][k]) if (b in model)!=(d in model)]
            assert len(selected)<=1;rec.append(selected[0] if selected else g[-1])
        p=axes(rec);assert validate(p)
        return 'FOUND',p,spent
def main():
    file,nt,layout,trials,quota,salt,freeze=sys.argv[1:];n=int(nt);rng=random.Random(int(salt));sizes=list(map(int,layout));assert sum(sizes)==9
    bank=[list(map(int,w)) for w in Path(file).read_text().split() if len(w)==n]
    stats=Counter();seen=set()
    for _ in range(int(trials)):
        row=rng.randrange(len(bank));ds=list(range(9));rng.shuffle(ds);groups=[]
        for k in sizes:groups.append(tuple(sorted(ds[:k])));ds=ds[k:]
        groups=tuple(sorted(groups));key=(row,groups)
        if key in seen:continue
        seen.add(key);st,p,c=run(bank[row],groups,int(quota),float(freeze),rng);stats[st]+=1
        print(json.dumps(dict(row=row,groups=groups,status=st,conflicts=c,**({'witness':p} if p else {}))),flush=True)
        if p:break
    print(json.dumps(dict(done=True,counts=stats)),flush=True)
if __name__=='__main__':main()
