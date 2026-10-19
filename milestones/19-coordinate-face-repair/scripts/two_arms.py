"""Compress a fixed 142-vertex middle path to one edge, then search both arms."""
import argparse
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
from exact_search import cp_model
from search_faces import sha

def check(path):
    assert len(path)==len(set(path))
    for j,v in enumerate(path):
        for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)

def run(args):
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    seed=json.loads(source.read_text())['path_vertices'];fixed=seed[50:]
    assert len(fixed)==142 and all(v>=128 for v in fixed)
    check(fixed)
    allowed=sorted(v for v in range(128) if all((v^w).bit_count()!=1 for w in fixed[1:-1]))
    roots=[next(v for v in range(128) if (v^w).bit_count()==1) for w in [fixed[0],fixed[-1]]]
    assert roots==[53,44] and set(roots)<=set(allowed)
    assert (roots[0]^roots[1]).bit_count()!=1
    assert all([v for v in range(128) if (v^w).bit_count()==1]==[r] for w,r in zip([fixed[0],fixed[-1]],roots))
    required=args.edges+1-len(fixed)
    m=cp_model.CpModel();x={v:m.new_bool_var(f'x{v}') for v in allowed}
    starts={v:m.new_bool_var(f's{v}') for v in allowed};ends={v:m.new_bool_var(f'e{v}') for v in allowed}
    edge_pairs=[(v,w) for i,v in enumerate(allowed) for w in allowed[i+1:] if (v^w).bit_count()==1]
    artificial=tuple(sorted(roots));edge_pairs.append(artificial)
    arcs=[(v,v,x[v].Not()) for v in allowed];directed={}
    neighbors={v:[] for v in allowed}
    for v,w in edge_pairs:
        neighbors[v].append(w);neighbors[w].append(v)
        a,b=m.new_bool_var(f'a{v}_{w}'),m.new_bool_var(f'a{w}_{v}')
        arcs.extend([(v,w,a),(w,v,b)]);directed[v,w]=a;directed[w,v]=b
        m.add(a+b>=x[v]+x[w]-1)
    for v in allowed:
        arcs.extend([(512,v,starts[v]),(v,512,ends[v])])
        m.add(starts[v]+ends[v]<=x[v])
        m.add(sum(x[w] for w in neighbors[v])==2-starts[v]-ends[v]).only_enforce_if(x[v])
    for r in roots:m.add(x[r]==1)
    if args.maximize:
        m.add(sum(x.values())<=required)
        m.maximize(sum(x.values()))
    else:m.add(sum(x.values())==required)
    m.add_circuit(arcs)
    for v in allowed:m.add_hint(x[v],int(v in roots))
    if args.control:
        for v in allowed:m.add(x[v]==int(v in roots))
    solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=args.seconds
    solver.parameters.num_search_workers=2;solver.parameters.random_seed=196
    status=solver.solve(m)
    report={'target_edges':args.edges,'maximize':args.maximize,'control':args.control,'fixed_path':fixed,'roots':roots,
            'allowed_inside':allowed,'required_inside_vertices':required,
            'source_sha256_lf':sha(source),'script_sha256_lf':sha(Path(__file__)),
            'status':solver.status_name(status),'seconds':solver.wall_time,
            'branches':solver.num_branches,'conflicts':solver.num_conflicts,
            'scope':'Both attachment vertices are selected; the fixed outside path is expanded into every feasible witness. No global bound is inferred.'}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        path=[next(v for v,a in starts.items() if solver.value(a))]
        while True:
            following=[w for (v,w),a in directed.items() if v==path[-1] and solver.value(a)]
            if not following:break
            assert len(following)==1 and following[0] not in path
            path.append(following[0])
        expanded=[path[0]];splices=0
        for v,w in zip(path,path[1:]):
            if (v,w)==tuple(roots):expanded.extend(fixed);splices+=1
            elif (w,v)==tuple(roots):expanded.extend(reversed(fixed));splices+=1
            expanded.append(w)
        assert splices==1 and len(path)<=required and len(expanded)<=args.edges+1
        if not args.maximize:assert len(path)==required and len(expanded)==args.edges+1
        check(expanded)
        report.update(compressed_path=path,path_vertices=expanded,actual_edges=len(expanded)-1)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:report[k] for k in ('target_edges','required_inside_vertices','status','seconds')}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--edges',type=int,default=196)
    p.add_argument('--seconds',type=float,default=60);p.add_argument('--control',action='store_true')
    p.add_argument('--maximize',action='store_true')
    p.add_argument('--output',type=Path,required=True);run(p.parse_args())
