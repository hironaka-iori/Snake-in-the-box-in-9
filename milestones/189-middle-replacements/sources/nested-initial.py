from pathlib import Path
import json,collections,itertools,sys,time,hashlib,argparse
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';P=R/'milestones/188-dimensional-constructions';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def project(v,k):return (v&((1<<k)-1))|((v>>(k+1))<<k)
def lift(v,k,b):return (v&((1<<k)-1))|((v>>k)<<(k+1))|(b<<k)
def check(p,n):
    assert len(p)==len(set(p)) and all(0<=v<1<<n for v in p)
    for i,u in enumerate(p):
        for j in range(i+1,len(p)):assert ((u^p[j]).bit_count()==1)==(j==i+1)
def prepare():
    parents=json.loads((H/'data/replacement-contexts.json').read_text())['rows'];rows=[]
    for idx,row in enumerate(parents):
        if row['middle_edges']!=95:continue
        p=row['middle'];options=[]
        for k in range(8):
            cuts=[i for i in range(95) if p[i]^p[i+1]==1<<k]
            if len(cuts)==2:options.append((k,cuts))
        assert len(options)==1
        k,(a,b)=options[0];inner=[project(v,k) for v in p[a+1:b+1]];ports={inner[0],inner[-1]};side=(p[a+1]>>k)&1
        fixed_inner_outer={project(v,k) for v in p[:a+1]+p[b+1:]};external={project(v,k) for v in row['left']+row['right'] if (v>>k)&1==side}
        forbidden=(fixed_inner_outer-ports)|external;allowed=sorted(set(range(128))-forbidden);assert set(inner)<=set(allowed);assert len(inner)==48
        check(inner,7);rows.append({'context_index':idx,'coordinate':k,'side':side,'cut_indices':[a,b],'ports':[inner[0],inner[-1]],'middle':inner,'allowed':allowed,'fixed_outer_projection':sorted(fixed_inner_outer),'external_forbidden':sorted(external),'fixed_prefix':p[:a+1],'fixed_suffix':p[b+1:],'parent_outer_left':row['left'],'parent_outer_right':row['right']})
    (H/'data/nested-contexts.json').write_text(json.dumps(rows,indent=2)+'\n')
    print('NESTED_COUNTS',dict(collections.Counter(len(r['allowed']) for r in rows)),flush=True)
    return rows
def solve(index,seconds):
    rows=json.loads((H/'data/nested-contexts.json').read_text());row=next(r for r in rows if r['context_index']==index);allowed=row['allowed'];s,t=row['ports'];model=cp_model.CpModel();x={v:model.new_bool_var('x'+str(v)) for v in allowed};idx={v:i for i,v in enumerate(allowed)}
    arcs=[(idx[v],idx[v],x[v].Not()) for v in allowed];directed={}
    for u in allowed:
        for k in range(7):
            v=u^(1<<k)
            if v not in x or v<=u:continue
            a=model.new_bool_var(f'a{u}_{v}');b=model.new_bool_var(f'a{v}_{u}');directed[u,v]=a;directed[v,u]=b;arcs.extend([(idx[u],idx[v],a),(idx[v],idx[u],b)])
            model.add(a+b<=x[u]);model.add(a+b<=x[v]);model.add(a+b>=x[u]+x[v]-1)
    model.add(x[s]==1);model.add(x[t]==1);arcs.append((idx[t],idx[s],True));model.add_circuit(arcs);model.add(sum(x.values())==50)
    current=set(row['middle'])
    for v,b in x.items():model.add_hint(b,int(v in current))
    tag=f'nested{index:02}-middle49';model.export_to_file(str(H/'data'/(tag+'.pbtxt')))
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=seconds;solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=189
    start=time.monotonic();status=solver.solve(model)
    report={'context_index':index,'target_nested_edges':49,'target_middle_edges':97,'target_full_edges':193,'allowed_vertices':len(allowed),'status':solver.status_name(status),'seconds':time.monotonic()-start,'time_limit':seconds,'branches':solver.num_branches,'conflicts':solver.num_conflicts,'model_sha256':hashlib.sha256((H/'data'/(tag+'.pbtxt')).read_bytes()).hexdigest(),'scope':'Only the47-edgeQ7component varies; all other nestedQ8components and externalQ9components and all crossing ports remain fixed. Solver exclusions have no Lean certificate.'}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        path=[s]
        while path[-1]!=t:
            opts=[v for (u,v),a in directed.items() if u==path[-1] and solver.value(a)];assert len(opts)==1 and opts[0] not in path;path.append(opts[0])
        check(path,7);assert len(path)==50
        middle=row['fixed_prefix']+[lift(v,row['coordinate'],row['side']) for v in path]+row['fixed_suffix'];check(middle,8);assert len(middle)==98
        joined=row['parent_outer_left']+[v+256 for v in middle]+row['parent_outer_right'];check(joined,9);assert len(joined)==194
        report.update(nested_vertices=path,middle_vertices=middle,joined_vertices=joined)
    (H/'data'/(tag+'.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if not isinstance(v,list)},indent=2),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--prepare',action='store_true');ap.add_argument('--index',type=int,default=0);ap.add_argument('--seconds',type=float,default=120);a=ap.parse_args()
    if a.prepare:prepare()
    else:solve(a.index,a.seconds)
