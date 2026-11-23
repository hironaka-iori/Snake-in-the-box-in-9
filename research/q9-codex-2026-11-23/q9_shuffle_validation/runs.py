from common import *
from itertools import combinations,permutations
import argparse,random,json,hashlib,sys
def bad(p):
    return [(i,j) for j,v in enumerate(p) for i,u in enumerate(p[:max(0,j-1)]) if (v^u).bit_count()<2]
def select(n,conf,rng,count):
    candidates=[(s,k) for k in (3,4) for s in range(n-k+1)]
    out=[];missing=set(conf)
    while len(out)<count and candidates:
        costs=[sum(s<i<s+k or s<j<s+k for i,j in missing) for s,k in candidates];v=max(costs)
        if v:ix=rng.choice([i for i,m in enumerate(costs) if m==v])
        else:ix=rng.randrange(len(candidates))
        s,k=candidates[ix];out.append((s,k));missing={p for p in missing if not (s<p[0]<s+k or s<p[1]<s+k)}
        candidates=[(t,z) for t,z in candidates if t+z<=s or s+k<=t]
    return sorted(out)
def sizes(n,spans):
    d=dict(spans);ls=[];j=0
    while j<n:k=d.get(j,1);ls.append(k);j+=k
    return ls
def exact(w,spans):
    # Boundary vertices stay fixed when only actual axes of each block can permute.
    p=vertices(w);spans=sorted(spans);mutable={s+t for s,k in spans for t in range(1,k)}
    fixed=[(j,v) for j,v in enumerate(p) if j not in mutable]
    def fine(i,a,j,b):return not (a==b or (((a^b).bit_count()==1)!=(abs(i-j)==1)))
    if any(not fine(i,a,j,b) for (i,a),(j,b) in combinations(fixed,2)):return None
    domain=[]
    for s,k in spans:
        options=[]
        for a in sorted(set(permutations(w[s:s+k]))):
            vals=[(s+t,p[s]^x) for t,x in enumerate(vertices(a)) if 0<t<k]
            if all(fine(i,x,j,y) for (i,x),(j,y) in combinations(vals,2)) and all(fine(i,x,j,y) for i,x in vals for j,y in fixed):options.append(vals)
        domain.append(options)
    domain.sort(key=len)
    def rec(j,added):
        if j==len(domain):
            q=p.copy()
            for t,v in added:q[t]=v
            return q
        for opts in domain[j]:
            if all(fine(i,x,t,v) for i,x in opts for t,v in added):
                q=rec(j+1,added+opts)
                if q:return q
    return rec(0,[])
def strictok(w,spans,p):
    q=word(p);indices=set()
    for s,k in spans:
        if sorted(q[s:s+k])!=sorted(w[s:s+k]):return False
        indices.update(range(s,s+k))
    return all(q[i]==a for i,a in enumerate(w) if i not in indices)
def run(mode,goal,count,seed,cap):
    rng=random.Random(seed);f=R/('q9_gap_generations/prior191.words' if mode=='control' else 'q9_via_q10/monotone_near.words')
    raw=[list(map(int,w)) for w in f.read_text().split() if len(w)==goal];ids=list(range(len(raw)));rng.shuffle(ids)
    cache={i:bad(vertices(w)) for i,w in enumerate(raw)};dest=D/f'{mode}{goal}_{seed}.jsonl';stat=Counter();literal=Counter()
    with dest.open('w') as out:
        for t in range(count):
            if t and t%len(ids)==0:rng.shuffle(ids)
            i=ids[t%len(ids)];w=raw[i].copy();axes=list(range(9));rng.shuffle(axes);pairs=[tuple(axes[j:j+2]) for j in range(0,8,2)];single=axes[-1]
            spans=select(goal,cache[i],rng,rng.choice((2,3,4,5) if mode=='control' else (4,5,6,7,8,10)))
            if mode=='control' and t%3:
                for s,k in spans:
                    z=w[s:s+k];rng.shuffle(z);w[s:s+k]=z
            lens=sizes(goal,spans);q=exact(w,spans);lit=bool(q);literal[str(lit)]+=1
            if q:assert induced(q,9) and strictok(w,spans,q)
            if mode=='control':assert lit
            st,p,c=solver.solve(w,pairs,single,lens,cap);stat[st]+=1
            if p:check(w,pairs,single,lens,p)
            if lit:assert st!='UNSAT'
            obj=dict(t=t,source=i,sha=hashlib.sha256(bytes(w)).hexdigest(),w=''.join(map(str,w)),spans=spans,pairs=pairs,single=single,errors=len(bad(vertices(w))) if mode=='control' else len(cache[i]),literal=lit,status=st,conflicts=c)
            if p:obj['path']=p
            if q:obj['literal_path']=q
            print(json.dumps(obj,separators=(',',':')),file=out,flush=True)
            if mode!='control' and (p or q):break
    print(json.dumps(dict(rows=t+1,model=stat,literal=literal)),flush=True)
if __name__=='__main__':run(sys.argv[1],*map(int,sys.argv[2:]))
