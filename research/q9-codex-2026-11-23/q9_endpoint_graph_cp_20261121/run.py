import argparse, collections, itertools, json, time, os
from pathlib import Path
from ortools.sat.python import cp_model
B=Path(__file__).resolve().parent; R=B.parent
ARCH=(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()
DATA=[json.loads(s) for s in (R/'q9_uncovered_endpoint_relocation.jsonl').read_text().splitlines()]
NB=[{v^(1<<i) for i in range(9)} for v in range(512)]
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def geometry(p):
    assert len(set(p))==len(p) and all(((u^v).bit_count()==1)==(i+1==j) for i,u in enumerate(p) for j,v in enumerate(p) if i<j)
def domain(row,c,control):
    p=path(ARCH[row['archive']]);ep=p[-1] if row['side'] else p[0]
    blockers=set(row['conflicts_with']); y=row['new_vertex']
    assert blockers==NB[y]&set(p)-{ep} and ep in NB[y]
    release={v for v in p if min((v^b).bit_count() for b in blockers)<=row['radius']}-{ep}
    assert len(release)==row['release']
    mandatory=(set(p)-release)|({y} if not control else set())
    excluded=blockers if not control else set()
    fixed=set(mandatory);blocked=set(excluded);remaining=set(range(512))
    while True:
        newpos=set();newneg=set();allowed=remaining-blocked
        for v in allowed:
            mindeg=1 if c is None or v.bit_count()%2==c else 2
            sure=NB[v]&fixed;possible=NB[v]&allowed
            if len(sure)>2 or len(possible)<mindeg:newneg.add(v)
            if v in fixed:
                if len(sure)==2:newneg|=NB[v]-sure
                if len(possible)==mindeg:newpos|=possible
        if (newpos|fixed)&(newneg|blocked):return None
        if newpos<=fixed and newneg<=blocked:break
        fixed|=newpos;blocked|=newneg
    return p,mandatory,excluded,fixed,blocked

def widths(fixed,blocked):
    free=set(range(512))-fixed-blocked
    # Remove vertices from the primal graph of unfixed local degree factors; cardinality rows are global.
    near={v:set() for v in free}
    for v in set(range(512))-blocked:
        scope=(NB[v]|{v})&free
        for u in scope:near[u].update(scope-{u})
    width=0
    while near:
        v=min(near,key=lambda x:(len(near[x]),x)); ns=near.pop(v);width=max(width,len(ns))
        for u in ns:near[u]=(near[u]|ns)-{v,u}
    return width,len(free)

def comp(s):
    rem=set(s); out=[]
    while rem:
        q=[rem.pop()]
        for v in q:
            t=NB[v]&rem;q.extend(t);rem-=t
        out.append(q)
    return out

def solve(row,c,control,secs,worker,circuit,faces):
    ret={'archive':row['archive'],'side':row['side'],'new_vertex':row['new_vertex'],'radius':row['radius'],'majority':c,'control':control}
    data=domain(row,c,control)
    if data is None:return ret|{'status':'PROP_INFEASIBLE'}
    ref,mandatory,excluded,fixed,blocked=data;allowed=set(range(512))-blocked;free=allowed-fixed
    n=192 if control else int(os.getenv('Q9_CP_VERTICES','193'))
    ret['target_vertices']=n
    m=cp_model.CpModel()
    x={v:(1 if v in fixed else m.new_bool_var(f'x{v}')) for v in sorted(allowed)}
    ends={v:m.new_bool_var(f't{v}') for v in sorted(allowed) if (c is None or v.bit_count()%2==c) and len(NB[v]&fixed)<2}
    for col in (0,1):
        take=[x[v] for v in allowed if v.bit_count()%2==col];m.add(sum(take)==(n//2+int(c==col)))
        m.add(sum(e for v,e in ends.items() if v.bit_count()%2==col)==(1 if c is None else 2*int(col==c)))
    incidence={v:[] for v in allowed};edges={}
    for v in sorted(allowed):
        for u in sorted(NB[v]&allowed):
            if u<=v:continue
            if v in fixed:z=x[u]
            elif u in fixed:z=x[v]
            else:
                z=m.new_bool_var(f'e{v}_{u}')
                m.add(z<=x[v]);m.add(z<=x[u]);m.add(z>=x[v]+x[u]-1)
            edges[(v,u)]=z;incidence[v].append(z);incidence[u].append(z)
    for v in allowed:m.add(sum(incidence[v])+ends.get(v,0)==2*x[v])
    m.add(sum(edges.values())==n-1)
    for v in sorted(allowed):
        for a,b in itertools.combinations(range(9),2):
            if v&(1<<a|1<<b):continue
            sq={v,v^1<<a,v^1<<b,v^1<<a^1<<b}
            if sq<=allowed and len(sq&free)>0:m.add(sum(x[q] for q in sq)<=3)
    if faces:
        # Every Q3 face induces an acyclic subgraph of degree at most two; precompute local occupancy bounds.
        for axes in itertools.combinations(range(9),3):
            bits=[1<<x for x in axes];mask=sum(bits);offset=[sum(b for i,b in enumerate(bits) if t>>i&1) for t in range(8)]
            for base in range(512):
                if base&mask:continue
                cell=[base^a for a in offset];ff=[v for v in cell if v in free]
                if len(ff)<3:continue
                hard={v for v in cell if v in fixed};best=-1
                for k in range(1<<len(ff)):
                    q=k.bit_count()
                    if q<=best:continue
                    ss=hard|{u for i,u in enumerate(ff) if k>>i&1}
                    if any(len(NB[v]&(ss|fixed))>2 for v in ss):continue
                    if any(sum(len(NB[v]&set(part)) for v in part)>=2*len(part) for part in comp(ss)):continue
                    best=q
                if best<len(ff):m.add(sum(x[q] for q in ff)<=best)
    if circuit:
        arcs=[]; idx={v:j+1 for j,v in enumerate(sorted(allowed))}
        for v in free:arcs.append((idx[v],idx[v],x[v].Not()))
        for (u,v),z in edges.items():
            a=m.new_bool_var('');b=m.new_bool_var('');m.add(a+b==z);arcs.extend([(idx[u],idx[v],a),(idx[v],idx[u],b)])
        for v,t in ends.items():
            a=m.new_bool_var('');b=m.new_bool_var('');m.add(a+b==t);arcs.extend([(0,idx[v],a),(idx[v],0,b)])
        m.add_circuit(arcs)
    refset=set(ref)
    for v in free:m.add_hint(x[v],int(v in refset))
    if control:
        for (v,u),z in edges.items():
            if v not in fixed and u not in fixed:m.add_hint(z,int(v in refset and u in refset))
        for v,t in ends.items():m.add_hint(t,int(v==ref[0] or v==ref[-1]))
    solver=cp_model.CpSolver();solver.parameters.num_workers=worker;solver.parameters.random_seed=12199
    solver.parameters.log_search_progress=False
    solver.parameters.linearization_level=int(os.getenv('Q9_CP_LP','1'))
    t=time.monotonic();cuts=0
    while True:
        left=secs-(time.monotonic()-t)
        if left<=0:status='UNKNOWN';break
        solver.parameters.max_time_in_seconds=left;s=solver.solve(m)
        status=solver.status_name(s)
        if s not in (cp_model.OPTIMAL,cp_model.FEASIBLE):break
        ss={v for v,a in x.items() if v in fixed or solver.value(a)}
        parts=comp(ss)
        if len(parts)==1:
            start=next(v for v in ss if len(NB[v]&ss)==1);p=[start];rem=ss-{start}
            while rem:
                nxt,=NB[p[-1]]&rem;p.append(nxt);rem.remove(nxt)
            assert len(p)==n and mandatory<=ss and not excluded&ss;geometry(p);ret['path']=p;status='FOUND';break
        for part in parts:
            if all(len(NB[v]&ss)==2 for v in part):
                rr=set(part)-fixed;m.add(sum(x[v] for v in rr)<len(rr));cuts+=1
    return ret|{'status':status,'seconds':round(time.monotonic()-t,3),'cuts':cuts,'fixed':len(fixed),'free':len(free),'conflicts':solver.num_conflicts,'branches':solver.num_branches}

def jobs():
    return [(r,b['majority']) for r in DATA for b in r['branches'] if b['status']=='UNKNOWN']
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--rank',action='store_true');ap.add_argument('--control',action='store_true');ap.add_argument('--secs',type=float,default=2);ap.add_argument('--workers',type=int,default=1);ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=119);ap.add_argument('--step',type=int,default=1);ap.add_argument('--circuit',action='store_true');ap.add_argument('--faces',action='store_true');a=ap.parse_args()
    pairs=jobs()
    if a.rank:
        ranked=[]
        for idx,(r,c) in enumerate(pairs):
            d=domain(r,c,False);w,count=(0,0) if d is None else widths(d[-2],d[-1]);ranked.append((w,count,idx))
        print(json.dumps(sorted(ranked)));exit()
    ranks=json.loads((B/'rank.json').read_text())
    for rank in range(a.start,min(a.stop,len(ranks)),a.step):
        width,count,i=ranks[rank];r,c=pairs[i]
        print(json.dumps(solve(r,None if a.control else c,a.control,a.secs,a.workers,a.circuit,a.faces)|{'rank':rank,'width_upper':width}),flush=True)
