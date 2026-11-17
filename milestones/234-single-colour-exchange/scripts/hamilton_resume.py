from pathlib import Path
import argparse,collections,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--per-query',type=float,default=2);a=ap.parse_args()
source=H/'data/remaining.json';raw=json.loads(source.read_bytes());assert all(sha(p)==h for p,h in raw['pins'].items())
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),results=[],witness=None,scope='Fix each saved96vertex class as the minority class of a193vertex induced path. Two-neighbour opposite vertices label internal edges; singleton-neighbour vertices label possible endpoints. Mandatory-dummy circuit arcs are allowed only at those endpoint-supported vertices. Entire opposite class andorderfree; no crossing or omission bound. Native exclusions are not Lean contradictions.')
def save():dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
started=time.monotonic();save()
for base in raw['bases']:
    if time.monotonic()-started>=a.seconds:break
    U=base['vertices'];S=set(U);c=U[0].bit_count()%2;n=len(U);assert n==96
    edges={};ports={};adj={v:set() for v in U}
    for z in range(512):
        if z.bit_count()%2==c:continue
        ns=sorted(S&{z^(1<<j) for j in range(9)})
        if len(ns)==1:ports.setdefault(ns[0],[]).append(z)
        elif len(ns)==2:
            v,w=ns;edges.setdefault((v,w),[]).append(z);adj[v].add(w);adj[w].add(v)
    row=dict(id=base['id'],ports=ports,edges=[[v,w,z] for (v,w),zs in edges.items() for z in zs],leaves=[v for v in U if len(adj[v])==1])
    out['results'].append(row)
    if len(ports)<2:row.update(status='FEWER_THAN_TWO_PORTS');continue
    if any(not adj[v] for v in U):row.update(status='ISOLATED',certificate=[v for v in U if not adj[v]]);continue
    if len(row['leaves'])>2:row.update(status='TOO_MANY_LEAVES');continue
    if any(v not in ports for v in row['leaves']):row.update(status='UNSUPPORTED_LEAF');continue
    reached={U[0]};stack=[U[0]]
    while stack:
        v=stack.pop()
        for w in adj[v]-reached:reached.add(w);stack.append(w)
    if len(reached)<n:row.update(status='DISCONNECTED',certificate=sorted(reached));continue
    index={v:i for i,v in enumerate(U)};m=cp_model.CpModel();arcs=[];variables={}
    for v,w in edges:
        for i,j in [(index[v],index[w]),(index[w],index[v])]:
            x=m.new_bool_var(f'a{i}_{j}');variables[i,j]=x;arcs.append((i,j,x))
    for v in ports:
        for i,j in [(index[v],n),(n,index[v])]:
            x=m.new_bool_var(f'a{i}_{j}');variables[i,j]=x;arcs.append((i,j,x))
    m.add_circuit(arcs);model=H/'data'/f'{a.tag}-{base["id"]:03d}.pbtxt';m.export_to_file(str(model));row.update(model=model.name,model_sha256=sha(model))
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=min(a.per_query,a.seconds-(time.monotonic()-started))
    status=solver.solve(m);row.update(status=solver.status_name(status),seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts)
    if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
        succ={i:j for (i,j),x in variables.items() if solver.value(x)};route=[];v=succ[n]
        while v!=n:
            assert v not in route;route.append(v);v=succ[v]
        assert len(route)==n;ordered=[U[i] for i in route];path=[ports[ordered[0]][0],ordered[0]]
        for v,w in zip(ordered,ordered[1:]):path.extend([edges[min(v,w),max(v,w)][0],w])
        path.append(ports[ordered[-1]][0]);assert len(path)==len(set(path))==193
        assert all(((v^path[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(path) for j in range(i+1,len(path)))
        row['status']='WITNESS';out['witness']=dict(base=base['id'],path=path,contracted_path=ordered);save();break
    if len(out['results'])%25==0:save()
out['status']='WITNESS' if out['witness'] else 'COMPLETE_QUERY_BATCH' if len(out['results'])==len(raw['bases']) else 'TIME_LIMIT'
out['statuses']=dict(collections.Counter(x['status'] for x in out['results']));out['seconds']=time.monotonic()-started;save();print(json.dumps({k:out[k] for k in ['status','statuses','seconds','witness']}),flush=True)
