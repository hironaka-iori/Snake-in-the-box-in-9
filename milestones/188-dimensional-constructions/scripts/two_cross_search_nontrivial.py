"""Search an opposite-face two-path forest with a fixed middle path."""
from pathlib import Path
import sys,json,time,argparse,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/188-dimensional-constructions'
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model

def project(v,k):return (v&((1<<k)-1))|((v>>(k+1))<<k)
def check(path,n):
    assert len(path)==len(set(path)) and all(0<=x<1<<n for x in path)
    for i,u in enumerate(path):
        for j in range(i+1,len(path)):assert ((u^path[j]).bit_count()==1)==(j==i+1)
def solve(n,middle,hint,target,seconds,tag):
    check(middle,n);N=1<<n;ports=[middle[0],middle[-1]]
    allowed=sorted(set(range(N))-(set(middle)-set(ports)))
    model=cp_model.CpModel();x={v:model.new_bool_var('x'+str(v)) for v in allowed}
    edge={};neighbors={v:[] for v in allowed};flow={}
    for u in allowed:
        for k in range(n):
            v=u^(1<<k)
            if v not in x or v<=u:continue
            e=model.new_bool_var(f'e{u}_{v}');edge[u,v]=e
            model.add(e<=x[u]);model.add(e<=x[v]);model.add(e>=x[u]+x[v]-1)
            neighbors[u].append((v,e));neighbors[v].append((u,e))
            for a,b in [(u,v),(v,u)]:
                f=model.new_int_var(0,N,f'f{a}_{b}');flow[a,b]=f;model.add(f<=N*e)
    for v in allowed:
        deg=sum(e for _,e in neighbors[v])
        model.add(deg>=x[v]);model.add(deg<=2*x[v])
        if v in ports:model.add(x[v]==1);model.add(deg==1)
        net=sum(flow[v,u]-flow[u,v] for u,_ in neighbors[v])
        if v in ports:
            supply=model.new_int_var(0,N,'supply'+str(v));model.add(net==supply-1)
        else:model.add(net==-x[v])
    model.add(sum(edge.values())==sum(x.values())-2)
    outside_vertices=target-(len(middle)-1)
    model.add(sum(x.values())>=outside_vertices)
    model.maximize(sum(x.values()))
    if hint:
        selected=set(hint)
        for v,z in x.items():model.add_hint(z,int(v in selected))
        for (u,v),z in edge.items():model.add_hint(z,int(u in selected and v in selected))
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1
    solver.parameters.max_time_in_seconds=seconds;solver.parameters.max_memory_in_mb=512
    solver.parameters.random_seed=188
    started=time.monotonic();status=solver.solve(model)
    report={'tag':tag,'base_dimension':n,'middle_edges':len(middle)-1,'target_edges':target,'allowed_vertices':len(allowed),
            'status':solver.status_name(status),'seconds':time.monotonic()-started,'time_limit':seconds,
            'best_outside_bound':solver.best_objective_bound,'branches':solver.num_branches,'conflicts':solver.num_conflicts,
            'middle':middle,'scope':'Fixed middle path, exactly two crossings, arbitrary induced opposite-face two-path forest; solver exclusions are not Lean certificates.'}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        chosen={v for v,z in x.items() if solver.value(z)};paths=[]
        for root in ports:
            path=[root];previous=None
            while True:
                opts=[v for v,_ in neighbors[path[-1]] if v in chosen and v!=previous]
                if not opts:break
                assert len(opts)==1 and opts[0] not in path
                previous=path[-1];path.append(opts[0])
            check(path,n);paths.append(path)
        assert not set(paths[0])&set(paths[1]) and set(paths[0])|set(paths[1])==chosen
        joined=paths[0][::-1]+[v+N for v in middle]+paths[1]
        check(joined,n+1);assert len(joined)-1>=target
        report.update(outside_paths=paths,outside_vertices=len(chosen),joined_edges=len(joined)-1,joined_vertices=joined)
    (H/'data'/f'{tag}.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['middle','joined_vertices','outside_paths']},indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('case',choices=['6to7','7to8','8to9']);args=ap.parse_args()
    seeds=json.loads((H/'data/lower-dimensional-seeds.json').read_text())
    if args.case=='6to7':
        q=seeds['7']['profiles'][0];middle=q['parts'][1]['path'];hint=q['parts'][0]['path']+q['parts'][2]['path']
        solve(6,middle,hint,50,30,'lift6to7-fixed24')
    elif args.case=='7to8':solve(7,seeds['7']['vertices'],None,98,60,'lift7to8-fixed50')
    else:
        row=json.loads((H/'data/middle-ancestry.json').read_text())['rows'][0]
        bank=json.loads((R/'work/bank9.json').read_text());p=bank[row['bank_index']]['vertex_sequence'];k=row['coordinate']
        cuts=[i for i in range(len(p)-1) if p[i]^p[i+1]==1<<k];a,b=cuts
        solve(8,[project(v,k) for v in p[a+1:b+1]],[project(v,k) for v in p[:a+1]+p[b+1:]],192,120,'lift8to9-fixed95')
