"""Revisit unresolved targeted regions with an induced-degree solver model."""
from pathlib import Path
import argparse,collections,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
from native_resources import snapshot
ap=argparse.ArgumentParser();ap.add_argument('--source',default='target34-64.json');ap.add_argument('--last',type=int,default=42)
ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--per-query',type=float,default=5)
ap.add_argument('--tag',default='retry36-42');a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data'/a.source;previous=json.loads(source.read_text());assert previous['status'] in ['COMPLETE','TIME_LIMIT']
bankraw=(H/'data/lower-input.json').read_bytes();bankhash=hashlib.sha256(bankraw).hexdigest()
assert bankhash==previous['bank_sha256']
bank=json.loads(bankraw)
N=[{v^(1<<k) for k in range(7)} for v in range(128)]
cases=[r['query'] for r in previous['unknown'] if r['query']['length']<=a.last]
begun=time.monotonic();cache={};results=[];witness=None
def valid(p):
    return len(set(p))==len(p) and all((((u^p[j]).bit_count()==1)==(j==i+1)) for i,u in enumerate(p) for j in range(i+1,len(p)))
def save(status):
    dest.write_text(json.dumps(dict(status=status,seconds=time.monotonic()-begun,arguments=vars(a),resource_gate=gate,
        bank_sha256=bankhash,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        total_queries=len(cases),completed_queries=len(results),unique_models=len(cache),results=results,witness=witness,
        scope='Retry only recorded UNKNOWN queries. Exact selected-vertex count, induced degrees at fixed anchors, colour counts and square exclusions. Disconnected longer cycles are cut when found. INFEASIBLE is a native solver result without a Lean contradiction certificate.'),indent=2)+'\n')
for number,query in enumerate(cases):
    if time.monotonic()-begun>=a.seconds:break
    p=bank[query['seed']]['vertex_sequence'];i=query['start'];j=query['end'];length=query['length'];u=p[i];v=p[j]
    endpoint=query['endpoint'];w=p[endpoint]^(1<<query['direction'])
    retained=p[:i+1]+p[j:]
    assert all(z!=w and z not in N[w] for z in retained if z!=p[endpoint])
    forbidden=set(retained)|N[w]|{w}
    for z in retained:
        if z!=u and z!=v:forbidden|=N[z]
    allowed=sorted((set(range(128))-forbidden)|{u,v})
    key=(u,v,length,tuple(allowed))
    if key in cache:
        old=results[cache[key]];results.append(dict(query=query,status=old['status'],reused_query=cache[key]));continue
    cache[key]=len(results);index=len(cache)-1;model=cp_model.CpModel();x={z:model.new_bool_var('x'+str(z)) for z in allowed}
    model.add(x[u]==1);model.add(x[v]==1);model.add(sum(x.values())==length+1)
    for z in allowed:model.add(sum(x[t] for t in N[z] if t in x)==(1 if z in [u,v] else 2)).only_enforce_if(x[z])
    startcolour=u.bit_count()%2
    model.add(sum(x[z] for z in allowed if z.bit_count()%2==startcolour)==(length+2)//2)
    squares=0
    for z in allowed:
        for bit1 in range(7):
            if z&(1<<bit1):continue
            for bit2 in range(bit1+1,7):
                if z&(1<<bit2):continue
                square=[z,z^(1<<bit1),z^(1<<bit2),z^(1<<bit1)^(1<<bit2)]
                if all(t in x for t in square):model.add(sum(x[t] for t in square)<=3);squares+=1
    modelpath=H/'data'/f'{a.tag}-model-{index:04d}.pbtxt';assert not modelpath.exists();model.export_to_file(str(modelpath))
    start=time.monotonic();iterations=[];cuts=[];status_name='UNKNOWN';route=None
    while time.monotonic()-start<a.per_query and time.monotonic()-begun<a.seconds:
        solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=512
        solver.parameters.max_time_in_seconds=max(.001,min(a.per_query-(time.monotonic()-start),a.seconds-(time.monotonic()-begun)))
        solver.parameters.random_seed=194
        status=solver.solve(model);status_name=solver.status_name(status)
        report=dict(status=status_name,seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts)
        iterations.append(report)
        if status not in [cp_model.FEASIBLE,cp_model.OPTIMAL]:break
        chosen={z for z in allowed if solver.value(x[z])};remaining=set(chosen);components=[]
        while remaining:
            z=min(remaining);part={z};todo=[z];remaining.remove(z)
            while todo:
                z=todo.pop()
                for t in N[z]&remaining:remaining.remove(t);part.add(t);todo.append(t)
            components.append(part)
        terminal=next(c for c in components if u in c);assert v in terminal
        cycles=[sorted(c) for c in components if u not in c]
        report['component_sizes']=[len(c) for c in components]
        if not cycles:
            route=[u]
            while route[-1]!=v:
                choices=(N[route[-1]]&chosen)-set(route[-2:]);assert len(choices)==1
                nxt=next(iter(choices));assert nxt not in route;route.append(nxt)
            q=p[:i]+route+p[j+1:];full=([w]+q) if endpoint==0 else (q+[w])
            assert len(route)==length+1 and len(full)==50 and valid(full)
            witness=dict(query=query,path=full,replacement=route);status_name='LONGER_WITNESS_FOUND';break
        for c in cycles:model.add(sum(x[z] for z in c)<=len(c)-1);cuts.append(c)
        status_name='UNKNOWN'
    result=dict(query=query,status=status_name,seconds=time.monotonic()-start,allowed=allowed,anchors=[u,v],
        target_vertices=length+1,square_cuts=squares,iterations=iterations,dynamic_cycle_cuts=cuts,
        model=str(modelpath),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest())
    results.append(result)
    if len(cache)%100==0 or len(cache)<=3:
        print(json.dumps(dict(queries=len(results),unique=len(cache),statuses=dict(collections.Counter(r['status'] for r in results)),seconds=time.monotonic()-begun)),flush=True)
        save('CHECKPOINT')
    if witness:break
save('LONGER_WITNESS_FOUND' if witness else 'COMPLETE' if len(results)==len(cases) else 'TIME_LIMIT')
print(json.dumps(dict(file=str(dest),queries=len(results),total=len(cases),unique=len(cache),statuses=dict(collections.Counter(r['status'] for r in results)),seconds=time.monotonic()-begun)),flush=True)
