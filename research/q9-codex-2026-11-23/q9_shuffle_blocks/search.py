"""Allow arbitrary reordering within consecutive blocks and recolor each step inside its axis group."""
from collections import Counter,defaultdict
from itertools import product,combinations
from pathlib import Path
import sys,random,json
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/'q9_pair_clocks'))
from search import axes,validate
from pysat.solvers import Cadical195

def solve(w,pairs,single,lengths,cap):
    n=len(w);ng=len(pairs);gr={a:i for i,pair in enumerate(pairs) for a in pair};gr[single]=ng
    counts=[0]*(ng+1);seq=[gr[a] for a in w];num=0;clauses=[];warm=[];indices=[]
    def var():
        nonlocal num
        num+=1;return num
    for _ in pairs:
        v=var();indices.append([v]);clauses.append([-v])
    physical=0
    for a,g in zip(w,seq):
        physical^=1<<a
        if g<ng:
            v=var();indices[g].append(v);lit=v if physical&1<<pairs[g][0] else -v;warm.append(lit)
            if len(indices[g])==2:clauses.append([lit])
    # Each feasible multiset prefix has a guard, or is compulsory at the block boundary.
    fibers=defaultdict(list);layers=[[] for _ in range(n+1)]
    def add(t,clocks,guard):
        mask=sum((x%2)<<g for g,x in enumerate(clocks));state=tuple(indices[g][clocks[g]] for g in range(ng))
        fibers[mask].append((t,state,guard));layers[t].append((clocks,guard))
    add(0,tuple(counts),None);t=0
    for length in lengths:
        tag=seq[t:t+length];numby=Counter(tag);active=sorted(numby)
        blocks=defaultdict(dict);origin=tuple(counts)
        for entries in product(*(range(numby[g]+1) for g in active)):
            depth=sum(entries)
            if not depth:continue
            v=None if depth==length else var();clock=counts.copy()
            for g,k in zip(active,entries):clock[g]+=k
            blocks[depth][entries]=v;add(t+depth,tuple(clock),v)
        for depth,options in blocks.items():
            ids=[x for x in options.values() if x is not None]
            if ids:
                clauses.append(ids);clauses.extend([[-x,-y] for x,y in combinations(ids,2)])
            for entries,x in options.items():
                if x is None or depth==1:continue
                prevs=[]
                for j,k in enumerate(entries):
                    if k:
                        q=list(entries);q[j]-=1;prevs.append(blocks[depth-1][tuple(q)])
                clauses.append([-x,*prevs])
        for g in tag:counts[g]+=1
        t+=length
    assert t==n
    aux={};req=set()
    for mask,states in fibers.items():
        for off in [-1,*range(ng+1)]:
            other=mask if off<0 else mask^1<<off
            if other<mask or other not in fibers:continue
            for t,x,u in states:
                for j,y,v in fibers[other]:
                    if abs(j-t)<2 or (other==mask and j<t):continue
                    q=[-z for z in (u,v) if z is not None]
                    for g,(a,b) in enumerate(zip(x,y)):
                        if a==b or g==off:continue
                        key=tuple(sorted((a,b)))
                        if key not in aux:
                            z=var();aux[key]=z;clauses.extend(([-z,a,b],[-z,-a,-b]))
                        q.append(aux[key])
                    if not q:return 'UNSAT',None,0
                    req.add(tuple(sorted(q)))
    clauses.extend(req)
    with Cadical195(bootstrap_with=clauses) as sol:
        sol.set_phases(warm);sol.conf_budget(cap);r=sol.solve_limited();k=sol.accum_stats()['conflicts']
        if r!=True:return ('UNSAT' if r is False else 'UNKNOWN'),None,k
        model=set(sol.get_model());p=[]
        for layer in layers:
            clocks=next(c for c,gate in layer if gate is None or gate in model)
            x=(clocks[ng]%2)<<single
            for g,(a,b) in enumerate(pairs):
                bit=int(indices[g][clocks[g]] in model);x|=bit<<a;x|=(bit^(clocks[g]%2))<<b
            p.append(x)
        assert len(p)==n+1 and validate(p);return 'FOUND',p,k
def make_lengths(n,size,offset):
    v=[offset] if offset else []
    while sum(v)<n:v.append(min(size,n-sum(v)))
    return v
def main(n,trials,seed,cap):
    rng=random.Random(seed);real=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
    raw=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    stat=Counter()
    for t in range(trials):
        if t%3==0:
            w=list(map(int,rng.choice(real)))
            while len(w)<n:w.insert(rng.randrange(len(w)+1),rng.randrange(9))
        else:w=rng.choice(raw)
        ds=list(range(9));rng.shuffle(ds);pairs=[tuple(ds[i:i+2]) for i in range(0,8,2)]
        k=rng.choice([3,4,5]);sizes=make_lengths(n,k,rng.randrange(k))
        st,p,c=solve(w,pairs,ds[8],sizes,cap);stat[st]+=1
        print(json.dumps(dict(trial=t,block=k,status=st,conflicts=c,**({'path':p,'source':w,'groups':pairs,'sizes':sizes} if p else {})),separators=(',',':')),flush=True)
        if p:break
    print(json.dumps(dict(done=True,counts=stat)),flush=True)
if __name__=='__main__':main(*map(int,sys.argv[1:]))
