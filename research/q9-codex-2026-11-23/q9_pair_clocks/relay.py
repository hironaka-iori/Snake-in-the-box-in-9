"""Change pair partitions repeatedly, carrying only independently checked simple walks."""
from search import axes,validate,partition,D,lift
from pysat.card import CardEnc,EncType
from pysat.solvers import Cadical195
from collections import Counter,defaultdict
from pathlib import Path
import json,sys,random
def shape(w):
    def c(a):
        table={}
        return ''.join(table.setdefault(z,str(len(table))) for z in a)
    return min(c(w),c(w[::-1]))
def defects(p):
    assert len(p)==len(set(p)) and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return {(i,j) for j,v in enumerate(p) for i,u in enumerate(p[:max(0,j-1)]) if (v^u).bit_count()==1}
def near(w,ps,s,quota,number,allowed,forbid):
    counts=Counter();idx={v:i for i,p in enumerate(ps) for v in p};idx[s]=4;cl=[];num=4;curr=list(range(1,5));cl.extend([[-v] for v in curr]);trace=[];m=0;at=defaultdict(list);phys=0;warm=[]
    for i in range(len(w)+1):
        if i:
            a=w[i-1];g=idx[a];m^=1<<g;phys^=1<<a
            if g<4:
                num+=1;curr[g]=num;lit=num if phys&(1<<ps[g][0]) else -num;warm.append(lit)
                if counts[g]==0:cl.append([lit])
                counts[g]+=1
        trace.append(tuple(curr));at[m].append(i)
    soft=[];aux={};hard=set()
    for m,L in at.items():
        for e in [-1,0,1,2,3,4]:
            o=m if e<0 else m^1<<e
            if o<m or o not in at:continue
            for i in L:
                for j in at[o]:
                    if abs(i-j)<=1 or (m==o and i>j):continue
                    ij=(min(i,j),max(i,j));q=[]
                    for g,(u,v) in enumerate(zip(trace[i],trace[j])):
                        if u==v or g==e:continue
                        key=tuple(sorted((u,v)))
                        if key not in aux:
                            num+=1;aux[key]=num;cl.extend(([-num,u,v],[-num,-u,-v]))
                        q.append(aux[key])
                    if e>=0 and ij not in forbid and (allowed is None or bool(allowed.intersection(ij))):
                        num+=1;soft.append(num);cl.append([*q,num])
                    elif q:hard.add(tuple(sorted(q)))
                    else:return 'UNSAT',None,None
    cl.extend(hard)
    if len(soft)>number:
        count=CardEnc.atmost(soft,bound=number,top_id=num,encoding=EncType.seqcounter);cl.extend(count.clauses)
    with Cadical195(bootstrap_with=cl) as sl:
        sl.set_phases(warm);sl.conf_budget(quota);r=sl.solve_limited()
        if r!=True:return ('UNKNOWN' if r is None else 'UNSAT'),None,None
        model=set(sl.get_model());path=[]
        for t,a in enumerate(w):
            g=idx[a]
            path.append(s if g==4 else ps[g][0 if (trace[t][g] in model)!=(trace[t+1][g] in model) else 1])
        cs=defects(axes(path));assert len(cs)<=number and not cs.intersection(forbid)
        return 'SAT',path,cs
def main():
    trials,seed,quota=map(int,sys.argv[1:]);rng=random.Random(seed)
    known=set((D.parent/'q9_via_q10/all_near_registered.words').read_text().split())
    queue=[];old=set()
    for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split():
        z=list(map(int,w))
        if len(z)!=192:continue
        cs=defects(axes(z))
        if len(cs)==2:queue.append((z,cs));old.add(shape(z))
    stats=Counter();added=0
    for t in range(trials):
        w,cs=rng.choice(queue);dims=list(range(9));rng.shuffle(dims);ps=[tuple(dims[j:j+2]) for j in range(0,8,2)];s=dims[-1]
        # First attempt the actual target. Only the follow-up step allows a defect.
        if t%5==0 or len(cs)==1 and t%2==0:
            st,p,k=lift(w,ps,s,quota);stats['hard_'+st]+=1
            if p:
                assert validate(p);print(json.dumps(dict(found=p,edges=len(p)-1)),flush=True);break
        else:
            keep=rng.choice(sorted(cs));forbid=cs-{keep} if t%3 else cs
            allowed={k+d for ij in cs for k in ij for d in range(-6,7)} if t%4 else None
            n=1 if len(cs)==1 or t%3 else 2
            st,v,bads=near(w,ps,s,quota,n,allowed,forbid);stats['relax_'+st]+=1
            if v:
                if not bads:
                    p=axes(v);assert validate(p);print(json.dumps(dict(found=p,edges=len(p)-1)),flush=True);break
                key=shape(v)
                if key not in old:
                    old.add(key);queue.append((v,bads));added+=1
                    print(json.dumps(dict(candidate=key,chords=len(bads),new_to_reference=key not in known,trial=t)),flush=True)
        if t%40==39:print(json.dumps(dict(trial=t+1,counts=stats,generated=added)),flush=True)
    print(json.dumps(dict(done=True,counts=stats,generated=added)),flush=True)
if __name__=='__main__':main()
