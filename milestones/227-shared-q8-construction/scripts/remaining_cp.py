"""Selected-vertex model for the five reduced Q8 path-pair tasks."""
from pathlib import Path
import argparse,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
def adjacent(u,v):return (u^v).bit_count()==1
def induced(p):return len(p)==len(set(p)) and all(adjacent(u,p[j])==(j==i+1) for i,u in enumerate(p) for j in range(i+1,len(p)))
N=[{v^(1<<k) for k in range(8)} for v in range(256)]
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,required=True);ap.add_argument('--per-query',type=float,default=30)
ap.add_argument('--ids',default='0,1,2,5,6,7,8,31,32,33,37,38,39,65,66,67,68,69,71,72,73,79,80,81,82,83,84,85,86,89,90,93,95,119,120,121,125,126,127,159,160,161,164,165,166,167,190,191,192,196,197,198');a=ap.parse_args()
source=H/'data/remaining-companions.json';j=json.loads(source.read_bytes());configs={c['id']:c for c in j['configurations']}
for p,h in j['pins'].items():assert sha(p)==h
raw=json.loads((H/'data/regions44.json').read_bytes());seed=raw['seed']
out=H/'data'/a.tag;out.mkdir(exist_ok=False)
result=dict(status='RUNNING',source_sha256=sha(source),script_sha256=sha(__file__),arguments=vars(a),results=[],witness=None,scope='Only specified reduced Q8 pair tasks. Selected degree constraints are relaxed by disconnected cycles; cycles are cut whenever found. Native infeasibility, no Lean contradiction certificate.')
start=time.monotonic()
for ident in map(int,a.ids.split(',')):
    if time.monotonic()-start>=a.seconds:break
    c=configs[ident];u,v=c['lower_anchors'];edges=[c['first_edges'],c['lower_edges']];anchors=[tuple(c['first_anchors']),(u,v)]
    f0,f1=anchors[0]
    domains=[set(c['first_domain'])-({u,v}|N[u]|N[v]),set(c['lower_domain'])-({f0,f1}|N[f0]|N[f1])]
    if any(not set(pair)<=domain for pair,domain in zip(anchors,domains)):
        result['results'].append(dict(id=ident,status='STATIC_INFEASIBLE',reason='Mandatory anchors conflict',seconds=0.0));save(out/'result.json',result);continue
    model=cp_model.CpModel();variables=[]
    for k,domain in enumerate(domains):
        x={z:model.new_bool_var(f'x{k}_{z}') for z in sorted(domain)};variables.append(x)
        x0,x1=anchors[k];assert {x0,x1}<=domain
        model.add(x[x0]==1);model.add(x[x1]==1);model.add(sum(x.values())==edges[k]+1)
        even=(edges[k]+2)//2 if x0.bit_count()%2==0 else (edges[k]+1)//2
        model.add(sum(val for z,val in x.items() if z.bit_count()%2==0)==even)
        for z in domain:model.add(sum(x[w] for w in N[z]&domain)==(1 if z in anchors[k] else 2)).only_enforce_if(x[z])
    for z in domains[0]:
        for w in (N[z]|{z})&domains[1]:model.add(variables[0][z]+variables[1][w]<=1)
    modelpath=out/f'model-{ident}.pbtxt';model.export_to_file(str(modelpath))
    row=dict(id=ident,status='RUNNING',domains=[len(x) for x in domains],edges=edges,model_sha256=sha(modelpath),iterations=[],cycle_cuts=[])
    result['results'].append(row);save(out/'result.json',result);qs=time.monotonic()
    while True:
        remain=min(a.per_query-(time.monotonic()-qs),a.seconds-(time.monotonic()-start))
        if remain<=0:row['status']='TIME_LIMIT';break
        solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=remain
        status=solver.solve(model);row['iterations'].append(dict(status=solver.status_name(status),seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts))
        if status not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:row['status']=solver.status_name(status);break
        paths=[];cyclefound=False
        for k,x in enumerate(variables):
            selected={z for z in x if solver.value(x[z])};route=[anchors[k][0]]
            while route[-1]!=anchors[k][1]:
                options=N[route[-1]]&selected-set(route[-2:]);assert len(options)==1
                z=next(iter(options));assert z not in route;route.append(z)
            assert induced(route);paths.append(route);remaining=selected-set(route)
            while remaining:
                stack=[min(remaining)];component=set()
                while stack:
                    z=stack.pop()
                    if z in component:continue
                    component.add(z);stack.extend(N[z]&remaining-component)
                assert all(len(N[z]&component)==2 for z in component)
                model.add(sum(x[z] for z in component)<=len(component)-1)
                row['cycle_cuts'].append(dict(part=k,vertices=sorted(component)));remaining-=component;cyclefound=True
        if cyclefound:save(out/'result.json',result);continue
        p,q=paths;assert [len(p),len(q)]==[x+1 for x in edges]
        first=p;second=c['upper_prefix']+q+c['upper_suffix'];(left,right),(other,end)=c['intervals']
        full=seed[:left]+first+seed[right+1:other]+second+seed[end+1:]+[24]
        assert len(full)==193 and induced(full) and sum((x^y)==256 for x,y in zip(full,full[1:]))==4
        row['status']='WITNESS';result['witness']=dict(config=ident,context=c['context'],first_lower=p,second_lower=q,path=full,edges=192);break
    row['seconds']=time.monotonic()-qs;save(out/'result.json',result)
    if result['witness']:break
result.update(status='WITNESS' if result['witness'] else 'COMPLETE_QUERY_BATCH' if len(result['results'])==len(a.ids.split(',')) else 'TIME_LIMIT',seconds=time.monotonic()-start)
save(out/'result.json',result)
print(json.dumps(dict(status=result['status'],results=[dict(id=x['id'],status=x['status'],seconds=x['seconds']) for x in result['results']])),flush=True)
