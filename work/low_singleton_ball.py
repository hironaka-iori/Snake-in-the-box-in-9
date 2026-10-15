"""Necessary ball constraints for a one-singleton snake with no endpoint near its root."""
import argparse,json,time
from itertools import combinations
from pathlib import Path
from exact_search import cp_model
from low_singleton_radius3 import components


def run(radius,seconds,endpoint_budget=2,exclude_cycles=True):
    assert 3<=radius<=9
    ball=[v for v in range(512) if v.bit_count()<=radius]
    fixed={0,1,2,5,10}|{(1<<a)|(1<<b) for a,b in combinations(range(2,9),2) if (a,b)!=(2,3)}
    m=cp_model.CpModel();x={v:m.new_bool_var(f'x{v}') for v in ball};ends=[]
    for v in ball:
        if v.bit_count()<=2:m.add(x[v]==int(v in fixed))
        neighbors=[v^(1<<k) for k in range(9) if v^(1<<k) in x]
        degree=sum(x[w] for w in neighbors)
        if v.bit_count()<radius:
            end=m.new_bool_var(f'end{v}');ends.append(end);m.add(end<=x[v])
            if v.bit_count()<=2:m.add(end==0)
            m.add(degree==2-end).only_enforce_if(x[v])
        else:m.add(degree<=2).only_enforce_if(x[v])
    m.add(sum(ends)<=endpoint_budget)
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.random_seed=29
    start=time.monotonic();cuts=0;iterations=[];cycle_clauses=[]
    while True:
        left=seconds-(time.monotonic()-start)
        if left<=0:status=cp_model.UNKNOWN;break
        solver.parameters.max_time_in_seconds=left
        status=solver.solve(m)
        iterations.append({'status':solver.status_name(status),'branches':solver.num_branches,'conflicts':solver.num_conflicts})
        if status not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:break
        selected=[v for v in ball if solver.value(x[v])]
        adj,parts=components(selected)
        cycles=[c['vertices'] for c in parts if c['cycle']]
        if not exclude_cycles or not cycles:break
        for cycle in cycles:
            m.add(sum(x[v] for v in cycle)<=len(cycle)-1);cuts+=1
            cycle_clauses.append(sorted(cycle))
    result={'radius':radius,'endpoint_budget':endpoint_budget,'exclude_cycles':exclude_cycles,
            'time_limit_seconds':seconds,'workers':1,'random_seed':29,'elapsed_seconds':time.monotonic()-start,
            'status':solver.status_name(status),'cycle_cuts':cuts,'cycle_clauses':cycle_clauses,'iterations':iterations,
            'scope':'Split-arm normalized radius-two selection; no endpoint within radius two; at most endpoint_budget interior endpoints. Boundary vertices may be local endpoints. Global connectivity is not required.',
            'verification':'Solver exclusions are not Lean-certified.'}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        assert all(len(adj[v])==2 for v in selected if v.bit_count()<=2)
        assert sum(len(adj[v])==1 for v in selected if v.bit_count()<radius)<=endpoint_budget
        assert all(len(adj[v])<=2 for v in selected)
        if exclude_cycles:assert all(not c['cycle'] for c in parts)
        result.update({'selected_vertices':selected,'components':parts})
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--radius',type=int,default=4);p.add_argument('--seconds',type=float,default=20)
    p.add_argument('--endpoint-budget',type=int,default=2);p.add_argument('--allow-cycles',action='store_true');args=p.parse_args()
    result=run(args.radius,args.seconds,args.endpoint_budget,not args.allow_cycles)
    suffix='_cycles' if args.allow_cycles else '_forest'
    Path(f'outputs/low_singleton_ball_r{args.radius}_e{args.endpoint_budget}{suffix}.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['selected_vertices','components','iterations']},indent=2))
    if 'components' in result:print('Components:',len(result['components']))
