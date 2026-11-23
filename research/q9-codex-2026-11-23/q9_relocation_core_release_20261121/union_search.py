from repair import *
from pysat.card import CardEnc,EncType
def search(rank,target,d,budget):
    r=rows[rank];p=allp[rank,0]+allp[rank,1];old=set(r['oldfixed']);best=None
    # Two geometrically different placements, one having the new vertex as an actual endpoint.
    for i,a in enumerate(allp[rank,0]):
        for j,b in enumerate(allp[rank,1]):
            A=set(a);Z=set(b);shared=old&A&Z
            if len(A^Z)<40:continue
            score=(len(shared),-abs(90-len(A^Z)), -i,-j)
            if best is None or score>best[0]:best=(score,a,b,shared,i,j)
    _,a,b,hard,ii,jj=best;g=set(a)|set(b);results=[]
    for c in ([None] if target==192 else [r['majority'],1-r['majority']]):
        F,x,ends,fixed=model(r,hard,target,c)
        other=[x[v] for v in x if v not in g];F.extend(CardEnc.atmost(other,d,top_id=F.nv,encoding=EncType.totalizer).clauses if d else [[-z] for z in other])
        cycles=0
        with Solver(name='cadical195',bootstrap_with=F) as sat:
            sat.set_phases([z if v in a else -z for v,z in x.items()])
            while True:
                cap=budget-sat.accum_stats()['conflicts']
                if cap<=0:ans=None;break
                sat.conf_budget(cap);ans=sat.solve_limited()
                if ans is not True:break
                bits=set(sat.get_model());ss={v for v,z in x.items() if z in bits};rem=set(ss);parts=[]
                while rem:
                    q=[rem.pop()]
                    for v in q:
                        new={v^1<<k for k in range(9)}&rem;q.extend(new);rem-=new
                    parts.append(q)
                if len(parts)==1:
                    u=next(v for v in ss if sum(v^1<<k in ss for k in range(9))==1);w=[u];rem=ss-{u}
                    while rem:
                        v,={w[-1]^1<<k for k in range(9)}&rem;w.append(v);rem.remove(v)
                    geometry(w);assert len(w)==target and fixed<=ss and len(ss-g)<=d and not ss&set(r['forbidden']);break
                for part in parts:
                    if all(sum(v^1<<k in ss for k in range(9))==2 for v in part):sat.add_clause([-x[v] for v in part]);cycles+=1
            yield dict(rank=rank,target=target,extra=d,c=c,union=len(g),kept=len(hard),first=ii,second=jj,freed=sorted(old-hard),result='FOUND' if ans else 'UNKNOWN' if ans is None else 'UNSAT',conflicts=sat.accum_stats()['conflicts'],cuts=cycles,path=w if ans else [])
allp=placements()
for rank in map(int,sys.argv[1:]):
    for n,e,budget in [(192,0,4000),(193,0,22000),(193,3,12000),(193,8,12000)]:
        for record in search(rank,n,e,budget):
            print(json.dumps(record),flush=True)
            if n==193 and record['result']=='FOUND':sys.exit()
