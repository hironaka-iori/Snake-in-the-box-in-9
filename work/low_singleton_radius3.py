"""A radius-three linear-forest relaxation of the endpoint-distance conjecture."""
import json,time
from itertools import combinations
from pathlib import Path
from exact_search import cp_model


def components(vertices):
    vertices=set(vertices)
    adj={v:[w for w in vertices if (v^w).bit_count()==1] for v in vertices}
    seen=set();result=[]
    for start in sorted(vertices):
        if start in seen: continue
        stack=[start];c=[]
        while stack:
            v=stack.pop()
            if v in seen:continue
            seen.add(v);c.append(v);stack.extend(adj[v])
        result.append({'vertices':sorted(c),'endpoints':[v for v in sorted(c) if len(adj[v])<=1],
                       'cycle':len(c)>1 and all(len(adj[v])==2 for v in c)})
    return adj,result


def run():
    # Root directions 0,1; missing pair 2,3; split arms 0+2 and 1+3.
    pair_vertices={sum(1<<k for k in ab) for ab in combinations(range(2,9),2)}-{12}
    pair_vertices|={5,10}
    fixed={0,1,2}|pair_vertices
    triples=[sum(1<<k for k in abc) for abc in combinations(range(9),3)]
    m=cp_model.CpModel();x={t:m.new_bool_var(f'x{t}') for t in triples}
    for t in triples:
        degree=sum((t^p).bit_count()==1 for p in fixed)
        if degree==0 or degree>2:m.add(x[t]==0)
    for p in pair_vertices:
        fixed_degree=sum((p^v).bit_count()==1 for v in fixed)
        m.add(sum(x[t] for t in triples if (p^t).bit_count()==1)==2-fixed_degree)
    m.minimize(sum(x.values()))
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1
    solver.parameters.random_seed=29;solver.parameters.max_time_in_seconds=10
    cuts=0;start=time.monotonic()
    while True:
        status=solver.solve(m)
        if status not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
            return {'status':solver.status_name(status),'cycle_cuts':cuts}
        selected=fixed|{t for t in triples if solver.value(x[t])}
        adj,parts=components(selected)
        cycles=[c['vertices'] for c in parts if c['cycle']]
        if not cycles:break
        for c in cycles:
            optional=[x[v] for v in c if v in x]
            assert optional
            m.add(sum(optional)<=len(optional)-1);cuts+=1
    assert all(len(adj[v])==2 for v in selected if v.bit_count()<=2)
    assert all(len(adj[v])<=2 for v in selected)
    assert all(not c['cycle'] for c in parts)
    alpha=sum(all(w not in selected for w in [1<<a,1<<b,(1<<a)|(1<<b)]) for a,b in combinations(range(9),2))
    assert alpha==1
    return {'status':'FEASIBLE_LOCAL_FOREST','elapsed_seconds':time.monotonic()-start,
            'radius':3,'selected_vertices':sorted(selected),'components':parts,'cycle_cuts':cuts,
            'singleton_count_at_zero':alpha,'all_selected_radius_two_vertices_degree_two':True,
            'limitation':'This disconnected induced linear forest in the radius-three ball is not a full Q9 snake. It shows these local constraints alone do not exclude the split-arm configuration.'}

if __name__=='__main__':
    result=run();Path('outputs/low_singleton_radius3.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print({k:v for k,v in result.items() if k not in ['selected_vertices','components']})
    if 'components' in result:print('Component sizes:',[len(c['vertices']) for c in result['components']])
