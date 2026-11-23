from collections import defaultdict,Counter
from search import axes,validate,D
from pysat.solvers import Cadical195
import random,json,sys
def solve(w,ps,s,a,b,cap,windows=None):
    ng=len(ps);grp={axis:i for i,g in enumerate(ps) for axis in g};grp[s]=ng
    num=ng;row=list(range(1,ng+1));frames=[];bucket=defaultdict(list);m=0;phys=0
    cnf=[[-v] for v in row];warm=[];visited=set()
    for i in range(len(w)+1):
        if i:
            axis=w[i-1];g=grp[axis];phys^=1<<axis;m^=1<<g
            if g<ng:
                num+=1;row[g]=num;lit=num if phys&(1<<ps[g][0]) else -num;warm.append(lit)
                if g not in (grp[a],grp[b]) and g not in visited:cnf.append([lit])
                visited.add(g)
        frames.append(tuple(row));bucket[m].append(i)
    n=len(w);cuts=[]
    for z in range(2):
        C=list(range(num+1,num+n+3));num=C[-1];cuts.append(C);cnf.extend(([-v,u] for u,v in zip(C,C[1:])));cnf.extend(([C[0]],[-C[-1]]))
        if windows:
            lo,hi=windows[z];cnf.extend(([C[lo]],[-C[hi+1]]))
    H,K=cuts;cnf.extend(([-x,y] for x,y in zip(H,K)))
    # Variables encode h>=i and k>=i. A boundary time belongs to both adjacent phases.
    def guard(phase,i,j):
        if phase==0:return [-H[j]]
        if phase==1:return [H[i+1],-K[j]]
        return [K[i+1]]
    physical=[0,1<<a,(1<<a)^(1<<b)];quot=[0,1<<grp[a],(1<<grp[a])^(1<<grp[b])]
    xs={};clauses=set()
    for ph in range(3):
        for end in range(ph,3):
            dx=physical[ph]^physical[end];dq=quot[ph]^quot[end]
            for mask,ts in bucket.items():
                for off in [-1,*range(ng+1)]:
                    other=mask^dq^(0 if off<0 else 1<<off)
                    if other not in bucket:continue
                    for i in ts:
                        for j in bucket[other]:
                            if j<i or j-i+end-ph<2:continue
                            if ph==end:cl=guard(ph,i,j)
                            else:cl=guard(ph,i,i)+guard(end,j,j)
                            taut=False
                            for g,(u,v) in enumerate(zip(frames[i],frames[j])):
                                if g==off:continue
                                if dx&(1<<ps[g][0]):v=-v
                                if u==-v:taut=True;break
                                if u==v:continue
                                key=min(tuple(sorted((u,v))),tuple(sorted((-u,-v))))
                                if key not in xs:
                                    num+=1;xs[key]=num;cnf.extend(([-num,u,v],[-num,-u,-v]))
                                cl.append(xs[key])
                            if not taut:clauses.add(tuple(sorted(set(cl))))
    cnf.extend(clauses)
    with Cadical195(bootstrap_with=cnf) as sol:
        sol.set_phases(warm);sol.conf_budget(cap);r=sol.solve_limited();c=sol.accum_stats()['conflicts']
        if r!=True:return ('UNSAT' if r is False else 'UNKNOWN'),None,None,c
        model=set(sol.get_model());h,k=[max(i for i,v in enumerate(C) if v in model) for C in cuts]
        out=[]
        for i,d in enumerate(w):
            g=grp[d];out.append(s if g==ng else ps[g][0 if (frames[i][g] in model)!=(frames[i+1][g] in model) else 1])
        out=out[:h]+[a]+out[h:k]+[b]+out[k:];p=axes(out)
        assert len(p)==len(w)+3 and validate(p);return 'FOUND',p,(h,k),c
def main(n,total,seed,cap):
    rng=random.Random(seed);mothers=[list(map(int,w)) for w in (D.parent/'q9_gap_generations/prior191.words').read_text().split()]
    near=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    stats=Counter()
    for t in range(total):
        if t%2==0:
            w=rng.choice(mothers).copy()
            while len(w)>n-2:w.pop(rng.randrange(len(w)))
            while len(w)<n-2:w.insert(rng.randrange(len(w)+1),rng.randrange(9))
        else:
            w=rng.choice(near).copy();p=axes(w);cs=[(i,j) for j,v in enumerate(p) for i,u in enumerate(p[:max(0,j-1)]) if (u^v).bit_count()<2];i,j=rng.choice(cs)
            for x in sorted((min(i,len(w)-1),min(j,len(w)-1)),reverse=True):w.pop(x)
        ds=list(range(9));rng.shuffle(ds);ps=[tuple(ds[j:j+2]) for j in range(0,8,2)];s=ds[-1];a,b=rng.choices(ds,k=2)
        st,p,h,c=solve(w,ps,s,a,b,cap);stats[st]+=1
        if p:print(json.dumps(dict(found=p,base=w,insert=(a,b),seams=h)),flush=True);break
        if t%10==9:print(json.dumps(dict(tested=t+1,counts=stats)),flush=True)
    print(json.dumps(dict(done=True,counts=stats)),flush=True)
if __name__=='__main__':main(*map(int,sys.argv[1:]))
