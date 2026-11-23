"""Lift valid Q9 archive paths into Q10 by an inverse, nonidentity two-chart assignment."""
import json,random
from pathlib import Path
from pysat.solvers import Minicard
D=Path(__file__).resolve().parent
rr=random.Random(412847)
bank=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
def valid(p):
    return len(set(p))==len(p) and all(((x^y).bit_count()==1)==(i==j+1) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
def tab(perm,off):
    z=[off]
    for k in perm:z.extend(x^(1<<k) for x in z[:])
    return z
def make(i,w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    assert valid(p)
    n=len(p)
    for attempt in range(240):
        m=list(range(9));ids=rr.sample(range(9),rr.choice((2,2,3,4)))
        for k in range(1,len(ids)):m[ids[0]],m[ids[k]]=m[ids[k]],m[ids[0]]
        j=rr.randrange(191);off=tab(m,0)[p[j]]^p[j+1];lookup=tab(m,off)
        inv=[0]*512
        for x,y in enumerate(lookup):inv[y]=x
        # A source index i in layer zero and j in layer one can coincide on their
        # Q9 part only when adjacent. Consecutive switches require this coincidence.
        with Minicard() as sat:
            switches=[]
            for j in range(n-1):
                a=j+1;b=j+2;s=n+j+1
                for cl in ([-a,-b,-s],[a,b,-s],[a,-b,s],[-a,b,s]):sat.add_clause(cl)
                if p[j]!=inv[p[j+1]]:sat.add_clause([a,-b])
                if inv[p[j]]!=p[j+1]:sat.add_clause([-a,b])
                switches.append(s)
            for a,x in enumerate(p):
                for b,q in enumerate(p):
                    if abs(a-b)>1 and x==inv[q]:sat.add_clause([a+1,-b-1])
            sat.add_atmost([-x for x in switches],len(switches)-(7+attempt%4))
            if not sat.solve():continue
            model=set(sat.get_model());tags=[int(j+1 in model) for j in range(n)];q=[inv[x]+512 if t else x for x,t in zip(p,tags)]
            assert valid(q);moved=sum(x!=y for x,y in zip(tags,tags[1:]))
            if len({(x^y).bit_length()-1 for x,y in zip(q,q[1:])})!=10:continue
            # Exclude every translation-only map for the declared cut coordinate.
            if any(valid([x^d if t else x for x,t in zip([v&511 for v in q],tags)]) for d in (1<<k for k in range(9))):continue
            return q,dict(archive_id=i,requested_permutation=m,requested_offset=off,switches=moved,axis=9)
if __name__=='__main__':
    jobs=[];meta=[]
    for i in rr.sample(range(len(bank)),len(bank)):
        val=make(i,bank[i])
        if val:
            q,z=val;jobs.append(q);meta.append(z)
        if len(jobs)==16:break
    (D/'controls.pts').write_text(''.join('10 '+' '.join(map(str,p))+'\n' for p in jobs))
    (D/'controls.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(len(jobs),[q['switches'] for q in meta])
