"""Insert an extra step at an unknown time while recoloring all paired coordinates."""
from pathlib import Path
import random,json,sys
from collections import defaultdict,Counter
from pysat.solvers import Cadical195
from search import partition,validate,axes,D

def solve(w,ps,s,extra,cap,window=None):
    gr={a:k for k,pair in enumerate(ps) for a in pair};glen=len(ps);gr[s]=glen
    n=len(w);gid=[gr[c] for c in w];base=[0]*glen;byclock=[];frames=[];mask=0
    cnt=0;warm=[];clauses=[]
    for g in range(glen):
        cnt+=1;base[g]=cnt;byclock.append([cnt]);clauses.append([-cnt]);warm.append(-cnt)
    fibers=defaultdict(list);physical=0
    for i in range(n+1):
        if i:
            c=w[i-1];g=gr[c];mask^=1<<g;physical^=1<<c
            if g<glen:
                cnt+=1;base[g]=cnt;byclock[g].append(cnt);warm.append(cnt if physical&(1<<ps[g][0]) else -cnt)
        fibers[mask].append(i);frames.append(tuple(base))
    for g,row in enumerate(byclock):
        if g!=extra and len(row)>1:clauses.append([row[1] if row[1] in warm else -row[1]])
    cut=list(range(cnt+1,cnt+n+3));cnt=cut[-1]
    clauses += [[cut[0]],[-cut[-1]]]+[[-y,x] for x,y in zip(cut,cut[1:])]
    if window is not None:
        lo,hi=window;clauses.extend(([cut[lo]],[-cut[hi+1]]))
    terms={};delta=1<<extra
    def test(i,j,diff,guards):
        nonlocal cnt
        cl=list(guards)
        for g,(a,b) in enumerate(zip(frames[i],frames[j])):
            if (diff>>g)&1 or a==b:continue
            key=(a,b) if a<b else (b,a)
            if key not in terms:
                cnt+=1;terms[key]=cnt;clauses.extend(([-cnt,a,b],[-cnt,-a,-b]))
            cl.append(terms[key])
        clauses.append(cl)
    for mask,ts in fibers.items():
        for change in [0,*[1<<g for g in range(glen+1)]]:
            for shift in (0,delta):
                other=mask^change^shift
                if other not in fibers or mask>other:continue
                for i in ts:
                    for j in fibers[other]:
                        if i==j or mask==other and i>j:continue
                        a=min(i,j);b=max(i,j)
                        if shift:test(a,b,change,[-cut[a],cut[b+1]])
                        elif b>a+1:
                            test(a,b,change,[-cut[b]])
                            test(a,b,change,[cut[a+1]])
    with Cadical195(bootstrap_with=clauses) as solver:
        solver.set_phases(warm);pending=[(0,n)];unknown=False;hits=False
        while pending:
            lo,hi=pending.pop();width=hi-lo+1
            solver.conf_budget(cap if width<9 else max(1000,cap//12))
            res=solver.solve_limited(assumptions=[cut[lo],-cut[hi+1]])
            if res is True:hits=True;break
            if res is False:continue
            if width==1:unknown=True;continue
            mid=(lo+hi)//2;pending.extend([(mid+1,hi),(lo,mid)])
        c=solver.accum_stats()['conflicts']
        if not hits:return ('UNKNOWN' if unknown else 'UNSAT'),None,None,c
        model=set(solver.get_model());h=max(i for i,x in enumerate(cut) if x in model)
        rec=[];ct=[0]*glen
        for g in gid:
            if g==glen:axis=s
            else:
                old=byclock[g][ct[g]];ct[g]+=1;new=byclock[g][ct[g]]
                axis=ps[g][0 if (old in model)!=(new in model) else 1]
            rec.append(axis)
        rec.insert(h,s if extra==glen else ps[extra][1]);out=axes(rec)
        assert validate(out) and len(out)==n+2
        return 'FOUND',out,h,c

def main():
    source,ns,trials,cap,seed=sys.argv[1:];n=int(ns);rng=random.Random(int(seed))
    bank=[list(map(int,w[:n])) for w in Path(source).read_text().split() if len(w)>=n]
    dim=tuple(range(9));parts=[(ps,s) for s in dim for ps in partition(tuple(x for x in dim if x!=s))]
    seen=set();counts=Counter()
    for _ in range(int(trials)):
        key=(rng.randrange(len(bank)),rng.randrange(len(parts)),rng.randrange(5))
        if key in seen:continue
        seen.add(key);row,k,e=key
        ps,s=parts[k];st,p,h,c=solve(bank[row],ps,s,e,int(cap));counts[st]+=1
        print(json.dumps(dict(row=row,partition=k,pairs=ps,single=s,extra=e,status=st,time=h,conflicts=c,**({'path':p} if p else {}))),flush=True)
        if p:break
    print(json.dumps(dict(done=True,counts=counts)),flush=True)
if __name__=='__main__':main()
