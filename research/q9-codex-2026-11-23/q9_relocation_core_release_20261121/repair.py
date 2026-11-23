import json,os,random,sys
from itertools import combinations
from pysat.card import CardEnc,EncType
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver
from prepare import B,geometry,path,bank
rows={r['rank']:r for r in json.loads((B/'branches.json').read_text())}
def placements():
    pp={}
    for l in (B/'placements.txt').read_text().splitlines():
        r,t,score,source,j,di,*p=map(int,l.split());geometry(p);rec=rows[r]
        assert len(p)==192 and p[j]==rec['ep'] and p[j+di]==rec['new_vertex'] and not set(p)&set(rec['forbidden'])
        assert len(set(p)&set(rec['oldfixed']))==score
        if t:assert p[j+di] in (p[0],p[-1])
        bucket=pp.setdefault((r,t),[])
        if not any(set(z)==set(p) for z in bucket):bucket.append(p)
    return pp
def model(r,hard,n=193,c=None,distance=None,guide=None):
    fixed=set(hard)|{r['ep'],r['new_vertex']};no=set(r['forbidden']);ng=lambda v:{v^(1<<i) for i in range(9)}
    for v in fixed:
        touched=ng(v)&fixed
        if len(touched)==2:no|=ng(v)-fixed
    assert not no&fixed
    pool=sorted(set(range(512))-no);nv=IDPool();x={v:nv.id(('v',v)) for v in pool}
    ends={v:nv.id(('e',v)) for v in pool if c is None or v.bit_count()%2==c};F=CNF()
    F.extend([[x[v]] for v in fixed])
    def exact(lits,k):
        if k<0 or k>len(lits):F.append([]);return
        if not k:F.extend([[-z] for z in lits]);return
        F.extend(CardEnc.equals(lits,k,vpool=nv,encoding=EncType.totalizer).clauses)
    for ko in (0,1):
        cv=[v for v in pool if v.bit_count()%2==ko]
        exact([x[v] for v in cv if v not in fixed],n//2+int(c==ko)-sum(v in fixed for v in cv))
        exact([ends[v] for v in cv if v in ends],1 if c is None else 2*int(c==ko))
    for v in pool:
        if v in ends:F.append([-ends[v],x[v]])
        nb=ng(v);q=2-len(nb&fixed);l=[x[w] for w in sorted(nb-fixed) if w in x]
        if v in ends:l.append(ends[v])
        if not 0<=q<=len(l):F.append([-x[v]]);continue
        F.extend([[-x[v]]+[-k for k in t] for t in combinations(l,q+1)])
        F.extend([[-x[v]]+list(t) for t in combinations(l,len(l)-q+1)])
    for i,j in combinations(range(9),2):
        for v in pool:
            if v&((1<<i)|(1<<j)):continue
            sq={v,v^1<<i,v^1<<j,v^1<<i^1<<j}
            if sq<=x.keys():F.append([-x[t] for t in sq-fixed])
    if distance is not None:
        g=set(guide);unavoidable=len(g-set(pool))
        lim=distance-unavoidable;ls=[-x[v] for v in sorted(g&set(pool)-fixed)]
        if lim<0:F.append([])
        elif lim<len(ls):F.extend(CardEnc.atmost(ls,lim,vpool=nv,encoding=EncType.totalizer).clauses)
    return F,x,ends,fixed
def solve(r,hard,guide,budget,majority,ass=(),distance=None,n=193):
    F,x,ends,fx=model(r,hard,n,majority,distance,guide);inverse={v:k for k,v in x.items()}
    aset=[x[v] for v in ass];g=set(guide);cycles=[];calls=0
    with Solver(name='cadical195',bootstrap_with=F) as sat:
        sat.set_phases([val if k in g else -val for k,val in x.items()])
        while True:
            left=budget-sat.accum_stats()['conflicts']
            if left<=0:ans=None;break
            sat.conf_budget(left);ans=sat.solve_limited(assumptions=aset);calls+=1
            if ans is not True:break
            m=set(sat.get_model());occ={v for v,z in x.items() if z in m};remain=set(occ);parts=[]
            while remain:
                p=[remain.pop()]
                for v in p:
                    nb={v^(1<<i) for i in range(9)}&remain;p.extend(nb);remain-=nb
                parts.append(p)
            if len(parts)==1:
                assert len(occ)==n and fx<=occ and set(ass)<=occ and not occ&set(r['forbidden'])
                ep=[v for v in occ if sum((v^1<<i in occ) for i in range(9))==1];assert len(ep)==2
                p=[ep[0]];remain=occ-set(p)
                while remain:
                    v,={p[-1]^1<<i for i in range(9)}&remain;p.append(v);remain.remove(v)
                geometry(p)
                return dict(result='FOUND',path=p,conflicts=sat.accum_stats()['conflicts'],cycles=cycles)
            for part in parts:
                if all(sum(v^1<<i in occ for i in range(9))==2 for v in part):
                    sat.add_clause([-x[t] for t in part]);cycles.append(sorted(part))
        uncore=[inverse[z] for z in (sat.get_core() or [])] if ans is False else None
        return dict(result='UNSAT' if ans is False else 'UNKNOWN',core=uncore,conflicts=sat.accum_stats()['conflicts'],cycles=cycles)
def window_sites(r,g,H):
    old=set(r['oldfixed']);old.discard(r['ep']);missing=old-set(g);p=path(bank[r['archive']]);pos={v:i for i,v in enumerate(p)}
    roots=sorted(missing,key=lambda v:(min((v^b).bit_count() for b in r['forbidden']),pos[v]))
    if not roots:return []
    return sorted(missing,key=lambda v:(min(abs(pos[v]-pos[z]) for z in roots[:2]),pos[v]))[:H]
if __name__=='__main__':
    mode=sys.argv[1];budget=int(sys.argv[2]);pp=placements()
    for rank in map(int,sys.argv[3:]):
        r=rows[rank];old=set(r['oldfixed']);stage=[]
        if mode in ('core','smallcore'):
            g=pp[rank,0][0];optional=window_sites(r,g,12 if mode=='core' else 6)
            z=solve(r,old-set(optional),g,budget,r['majority'],optional)
            print(json.dumps(dict(rank=rank,mode=mode,c=r['majority'],optional=optional,**z)),flush=True)
        else:
            for t in (0,1):
                g=pp[rank,t][0];hard=old&set(g);delta=sorted(old-hard)
                if mode=='target':configs=[(r['majority'],None),(1-r['majority'],None)]
                elif mode=='near':configs=[(c,d) for d in (5,10) for c in (0,1)]
                elif mode=='planted':configs=[(None,0)]
                else:raise ValueError(mode)
                for c,d in configs:
                    z=solve(r,hard,g,budget,c,distance=d,n=192 if c is None else 193)
                    print(json.dumps(dict(rank=rank,mode=mode,endpoint=t,c=c,distance=d,freed=delta,**z)),flush=True)
                    if c is not None and z['result']=='FOUND':sys.exit()
