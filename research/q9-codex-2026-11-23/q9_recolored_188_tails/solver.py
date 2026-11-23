from collections import defaultdict
from pysat.solvers import Cadical195

def solve(word,pairs,single,left,right,cap):
    dim=len(pairs)*2+1; ng=len(pairs)
    group={d:k for k,row in enumerate(pairs) for d in row};group[single]=ng
    axes=[group[c] for c in word];n=len(word);num=ng
    st=list(range(1,ng+1));phase=[-k for k in st];clauses=[[k] for k in phase]
    mask=actual=0;frames=[(mask,tuple(st))];seen=set()
    def var():
        nonlocal num
        num+=1;return num
    for a,g in zip(word,axes):
        mask^=1<<g;actual^=1<<a
        if g<ng:
            z=var();st[g]=z;sgn=z if actual>>pairs[g][0]&1 else -z
            phase.append(sgn)
            if g not in seen:
                clauses.append([sgn]);seen.add(g)
        frames.append((mask,tuple(st)))
    grouped=[0]*(1<<dim)
    for v in range(1,1<<dim):
        low=v&-v;grouped[v]=grouped[v^low]^(1<<group[low.bit_length()-1])
    cache={};protected=set()
    def protect(X,Y,guards=()):
        delta=X[0]^Y[0]
        if delta.bit_count()>1:return
        omitted=delta.bit_length()-1
        out=[]
        for k,(a,b) in enumerate(zip(X[1],Y[1])):
            if k==omitted or a==b:continue
            if a==-b:return
            relation=(min(abs(a),abs(b)),max(abs(a),abs(b)),(a<0)^(b<0))
            if relation not in cache:
                t=var();cache[relation]=t
                clauses.extend(([-t,a,b],[-t,-a,-b]))
            out.append(cache[relation])
        c=tuple(sorted(out))+guards
        if c not in protected:clauses.append(c);protected.add(c)
    aliases=defaultdict(list)
    for i,F in enumerate(frames):
        for flag in range(-1,ng+1):
            key=F[0]^(1<<flag if flag>=0 else 0)
            for j in aliases[key]:
                if i-j>1:protect(F,frames[j])
        aliases[F[0]].append(i)
    def shifted(base,offset):
        return base[0]^grouped[offset],tuple(-v if offset>>pairs[k][0]&1 else v for k,v in enumerate(base[1]))
    def arm(tip,depth):
        layers=[];prev={0:None}
        for i in range(1,depth+1):
            choices={v:var() for v in range(1<<dim) if 0<v.bit_count()<=i and (v.bit_count()-i)%2==0 and (i==1 or v.bit_count()>1)}
            clauses.append(list(choices.values()))
            # Sequential at-most-one with a prefix OR flag.
            last=None
            for z in choices.values():
                if last is not None:clauses.append([-last,-z])
                nxt=var();clauses.append([-z,nxt])
                if last is not None:clauses.append([-last,nxt])
                last=nxt
            bucket=defaultdict(list)
            for v,z in choices.items():
                F=shifted(frames[tip],v);bucket[F[0]].append((v,z,F))
                if i>1:clauses.append([-z]+[prev[v^(1<<k)] for k in range(dim) if v^(1<<k) in prev])
                for old,_ in layers[:-1]:
                    for u in (v,*(v^1<<k for k in range(dim))):
                        if u in old:clauses.append([-z,-old[u]])
                for flag in range(-1,ng+1):
                    key=F[0]^(1<<flag if flag>=0 else 0)
                    for j in aliases[key]:
                        if tip!=j or i>1:protect(F,frames[j],(-z,))
            layers.append((choices,bucket));prev=choices
        return layers
    L=arm(0,left);R=arm(n,right)
    for opts,buckets in L:
        for v,z in opts.items():
            F=shifted(frames[0],v)
            for _,other in R:
                for flag in range(-1,ng+1):
                    key=F[0]^(1<<flag if flag>=0 else 0)
                    for u,t,G in other[key]:protect(F,G,(-z,-t))
    with Cadical195(bootstrap_with=clauses) as sat:
        sat.set_phases(phase);sat.conf_budget(cap);res=sat.solve_limited()
        conflicts=sat.accum_stats()['conflicts']
        if res is not True:return ('UNSAT' if res is False else 'UNKNOWN'),None,conflicts
        model=set(sat.get_model())
    core=[]
    for m,F in frames:
        x=((m>>ng)&1)<<single
        for k,(a,b) in enumerate(pairs):
            first=F[k] in model
            if first:x|=1<<a
            if first^((m>>k)&1):x|=1<<b
        core.append(x)
    def extract(ls):
        return [next(v for v,z in opts.items() if z in model) for opts,_ in ls]
    return 'FOUND',[core[0]^v for v in reversed(extract(L))]+core+[core[-1]^v for v in extract(R)],conflicts
