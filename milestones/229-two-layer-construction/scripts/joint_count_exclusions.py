"""Reconnect two retained-index blocks jointly and append endpoint24."""
from pathlib import Path
import argparse,collections,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--ids',required=True);ap.add_argument('--width',type=int,required=True);ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=150);ap.add_argument('--per-query',type=float,default=2);a=ap.parse_args()
assert a.width==46
coverpath=H/'data/coverage46.json';cover=json.loads(coverpath.read_bytes())
assert cover['status']=='COMPLETE_NATIVE_EXCLUSION' and cover['width']==46 and cover['contexts']==315
assert all(sha(p)==h for p,h in cover['pins'].items())
sixpath=H/'data/six46.json';six=json.loads(sixpath.read_bytes());execution=json.loads((H/'data/six46-execution.json').read_bytes())
assert execution['status']=='ACCEPTED_NATIVE_RESULT' and execution['exit_code']==0 and execution['stop_reason'] is None
assert sha(sixpath)==execution['result_sha256'] and all(sha(p)==h for p,h in execution['pins'].items())
excluded_six={r['id'] for r in six['results'] if r['status']=='INFEASIBLE'}
assert len(excluded_six)==200 and six['witness'] is None
source=H/'data'/f'regions{a.width}.json';raw=json.loads(source.read_bytes());p=raw['seed'];N=[{v^(1<<k) for k in range(9)} for v in range(512)]
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),results=[],witness=None,total_contexts=len(a.ids.split(',')),scope='Two specified equal-width replacements of the specified seed, retaining all outside indices and anchors, then append24. Only the specified prepared width46contexts are searched. No boundary-change cut is imposed. The complete same-width four-crossing native cover forbids totalfour, and each completed same-context six-crossing result forbids totalsix. Other crossing counts remain permitted. Zero-face shortages impose necessary crossing minima. No total crossing count is prescribed. Per-part crossing parity and same-face capacity minima remain necessary; the parity variable bound uses the actual number of available vertical edges, not a saved crossing budget. No mutualcontact restriction or short-move closure premise. Native solver exclusions are not Lean-certified.')
start=time.monotonic()
def save():dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save()
for row in raw['contexts']:
    if row['id'] not in [int(x) for x in a.ids.split(',')]:continue
    if time.monotonic()-start>=a.seconds:break
    if row['status']=='INHERITED_EXCLUDED':
        out['results'].append(dict(id=row['id'],status='INHERITED_EXCLUDED',parent_id=row['parent_id'],parent_status=row['parent_status']));continue
    if row['status']=='STATIC_EXCLUDED':
        out['results'].append(dict(id=row['id'],status='STATIC_EXCLUDED',reasons=[r['rejections'] for r in row['parts']]));continue
    model=cp_model.CpModel();variables=[];crosses=[];all_cross_edges=[];conflict_count=0
    for k,part in enumerate(row['parts']):
        values=part['allowed'];u,v=part['anchors'];x={z:model.new_bool_var(f'x{k}_{z}') for z in values};variables.append(x)
        model.add(x[u]==1);model.add(x[v]==1);model.add(sum(x.values())==part['target_vertices'])
        for z in values:
            model.add(sum(x[w] for w in N[z] if w in x)==(1 if z in [u,v] else 2)).only_enforce_if(x[z])
            model.add_hint(x[z],int(z in p[part['interval'][0]:part['interval'][1]+1]))
        model.add(sum(x[z] for z in values if z.bit_count()%2==0)==part['required_even'])
        edges=[]
        for z in values:
            w=z^256
            if z<w and w in x:
                edge=model.new_bool_var(f'cross{k}_{z}');model.add(edge<=x[z]);model.add(edge<=x[w]);model.add(edge>=x[z]+x[w]-1);edges.append(edge)
        parity=int(bool(u&256)!=bool(v&256))
        half=model.new_int_var(0,len(edges)//2,f'cross_pairs{k}')
        model.add(sum(edges)==parity+2*half)
        if parity==0 and sum((z&256)==(u&256) for z in values)<part['target_vertices']:model.add(sum(edges)>=2)
        all_cross_edges.extend(edges);crosses.append(len(edges))
    model.add(sum(all_cross_edges)!=row['replacement_crossings'])
    if row['id'] in excluded_six:model.add(sum(all_cross_edges)!=row['replacement_crossings']+2)
    for u in variables[0]:
        for v in variables[1]:
            if u==v or v in N[u]:model.add(variables[0][u]+variables[1][v]<=1);conflict_count+=1
    modelpath=H/'data'/f'{a.tag}-{row["id"]:03d}.pbtxt';model.export_to_file(str(modelpath))
    record=dict(id=row['id'],intervals=row['intervals'],status='RUNNING',allowed_sizes=[len(x) for x in variables],cross_conflicts=conflict_count,model_sha256=sha(modelpath),model=modelpath.name,iterations=[],cycle_cuts=[])
    out['results'].append(record);save();query_start=time.monotonic()
    while True:
        remaining=min(a.per_query-(time.monotonic()-query_start),a.seconds-(time.monotonic()-start))
        if remaining<=0:record['status']='TIME_LIMIT';break
        solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=remaining
        status=solver.solve(model);name=solver.status_name(status)
        iteration=dict(status=name,seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts);record['iterations'].append(iteration)
        if status not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:record['status']=name;break
        routes=[];cycles=[]
        for k,x in enumerate(variables):
            selected={z for z in x if solver.value(x[z])};u,v=row['parts'][k]['anchors'];route=[u]
            while route[-1]!=v:
                options=(N[route[-1]]&selected)-set(route[-2:]);assert len(options)==1
                z=next(iter(options));assert z not in route;route.append(z)
            rest=selected-set(route)
            while rest:
                todo=[min(rest)];component=set()
                while todo:
                    z=todo.pop()
                    if z in component:continue
                    component.add(z);rest.remove(z);todo.extend(w for w in N[z]&selected if w not in component)
                assert all(len(N[z]&component)==2 for z in component)
                cycles.append((k,sorted(component)))
            routes.append(route)
        if cycles:
            for k,c in cycles:model.add(sum(variables[k][z] for z in c)<=len(c)-1);record['cycle_cuts'].append(dict(part=k,vertices=c))
            iteration['cycles']=len(cycles);record['status']='PENDING_CYCLE_CUT';save();continue
        (aa,bb),(cc,dd)=row['intervals'];path=p[:aa]+routes[0]+p[bb+1:cc]+routes[1]+p[dd+1:]+[24]
        assert len(path)==len(set(path))==193
        assert all(((u^path[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(path) for j in range(i+1,len(path)))
        actual_crossings=sum(u^v==256 for u,v in zip(path,path[1:]))
        out['witness']=dict(context=row['id'],path=path,replacements=routes,total_bit8_crossings=actual_crossings);record['status']='WITNESS';break
    record['seconds']=time.monotonic()-query_start;save()
    if out['witness']:break
out['status']='WITNESS' if out['witness'] else 'COMPLETE_COVERAGE' if len(out['results'])==out['total_contexts'] else 'TIME_LIMIT'
out['seconds']=time.monotonic()-start;out['statuses']=dict(collections.Counter(r['status'] for r in out['results']));save()
print(json.dumps({k:out[k] for k in ['status','seconds','statuses','total_contexts','witness']}),flush=True)
