"""Search every surviving fixed-colour contraction graph for a Hamiltonian path."""
from pathlib import Path
import argparse,collections,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=150);ap.add_argument('--per-query',type=float,default=2);a=ap.parse_args()
source=H/'data/colour-survey.json';raw=json.loads(source.read_bytes());assert raw['status']=='COMPLETE_SURVEY'
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),results=[],witness=None,scope='All49 surviving97vertex contraction graphs. Add a mandatory dummy vertex and solve one directed circuit through every graph vertex and dummy, with no self loops. Removing dummy gives a Hamiltonian path. Parallel labels are interchangeable because their selected opposite-colour neighbour pairs agree. Every accepted lifted193vertex path receives full pairwise inducedness verification. Native INFEASIBLE is not a Lean contradiction certificate.')
def save():dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
start=time.monotonic();save()
for graph in raw['survivors']:
    if time.monotonic()-start>=a.seconds:break
    U=graph['vertices'];index={v:i for i,v in enumerate(U)};labels={}
    for v,w,z in graph['edges']:labels.setdefault((min(v,w),max(v,w)),[]).append(z)
    n=len(U);assert n==97;m=cp_model.CpModel();arcs=[];variables={}
    for v,w in labels:
        i,j=index[v],index[w]
        for p,q in [(i,j),(j,i)]:
            x=m.new_bool_var(f'a{p}_{q}');variables[p,q]=x;arcs.append((p,q,x))
    for i in range(n):
        for p,q in [(i,n),(n,i)]:
            x=m.new_bool_var(f'a{p}_{q}');variables[p,q]=x;arcs.append((p,q,x))
    m.add_circuit(arcs)
    model=H/'data'/f'{a.tag}-{graph["id"]:05d}.pbtxt';m.export_to_file(str(model))
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=min(a.per_query,a.seconds-(time.monotonic()-start))
    status=solver.solve(m)
    row=dict(id=graph['id'],status=solver.status_name(status),seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts,model=model.name,model_sha256=sha(model))
    out['results'].append(row)
    if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
        succ={i:j for (i,j),x in variables.items() if solver.value(x)};route=[];v=succ[n]
        while v!=n:
            assert v not in route;route.append(v);v=succ[v]
        assert len(route)==n
        ordered=[U[i] for i in route];path=[ordered[0]]
        for v,w in zip(ordered,ordered[1:]):path.extend([labels[min(v,w),max(v,w)][0],w])
        assert len(path)==len(set(path))==193
        assert all(((v^path[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(path) for j in range(i+1,len(path)))
        out['witness']=dict(case=graph['id'],path=path,contracted_path=ordered);row['status']='WITNESS';save();break
    save()
out['status']='WITNESS' if out['witness'] else 'COMPLETE_QUERY_BATCH' if len(out['results'])==len(raw['survivors']) else 'TIME_LIMIT'
out['statuses']=dict(collections.Counter(r['status'] for r in out['results']));out['seconds']=time.monotonic()-start;save()
print(json.dumps({k:out[k] for k in ['status','statuses','seconds','witness']}),flush=True)
