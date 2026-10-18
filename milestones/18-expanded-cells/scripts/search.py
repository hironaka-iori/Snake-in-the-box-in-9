"""Search the full cube with a budget on vertices outside the base palette."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
from neighborhood_search import model
from exact_search import cp_model
from check_snake import verify

def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()

def run(args):
    seed_path=HERE/'data/aligned-seed.json'
    source=json.loads(seed_path.read_text())
    path=source['path_vertices']
    if path[0]>path[-1]:path=list(reversed(path))
    occupied=set(path)
    table_path=ROOT/'milestones/16-cycle-reservoirs/data/cell-states.json'
    tables=json.loads(table_path.read_text())['tables']
    palette={h*32+v for h in range(16) for v in tables[h.bit_count()%2]['vertices']}
    outside=set(range(512))-palette
    m,x,starts,arcs=model(9,args.edges,path,args.removed)
    m.add(sum(x[v] for v in outside)<=args.outside)
    cut_source=ROOT/'milestones/17-global-cell-construction/data/cycle-control.json'
    cuts=json.loads(cut_source.read_text())['initial_cycles']
    for c in cuts:m.add(sum(x[v] for v in c)<=len(c)-1)
    # Supply the known path orientation as well as its vertex set.
    used_arcs=set(zip(path,path[1:]))
    for v,a in enumerate(starts):m.add_hint(a,int(v==path[0]))
    for edge,a in arcs.items():m.add_hint(a,int(edge in used_arcs))
    if args.control:
        for v in range(512):m.add(x[v]==int(v in occupied))
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=args.seconds
    solver.parameters.num_search_workers=2
    solver.parameters.random_seed=196
    status=solver.solve(m)
    out={'target_edges':args.edges,'max_removed':args.removed,'max_outside':args.outside,
         'control':args.control,'seed_bank_index':source['bank_index'],
         'seed_sha256_lf':sha(seed_path),'table_sha256_lf':sha(table_path),
         'cut_source_sha256_lf':sha(cut_source),'driver_sha256_lf':sha(Path(__file__)),
         'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),
         'status':solver.status_name(status),'seconds':solver.wall_time,
         'branches':solver.num_branches,'conflicts':solver.num_conflicts,
         'scope':'Full-cube search restricted by an outside-palette budget and seed-deletion budget; UNKNOWN is unresolved.'}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        result=[next(v for v,a in enumerate(starts) if solver.value(a))]
        while True:
            following=[w for (v,w),a in arcs.items() if v==result[-1] and solver.value(a)]
            if not following:break
            assert len(following)==1 and following[0] not in result
            result.append(following[0])
        checked=verify([(v^w).bit_length()-1 for v,w in zip(result,result[1:])],9)
        assert checked['edges']==args.edges and checked['vertex_sequence']==[v^result[0] for v in result]
        assert len(occupied-set(result))<=args.removed
        assert len(set(result)&outside)<=args.outside
        out.update(path_vertices=result,outside_vertices=sorted(set(result)&outside),
                   removed_vertices=sorted(occupied-set(result)),added_vertices=sorted(set(result)-occupied),
                   pairs_checked=checked['pairs_checked'])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:out[k] for k in ('target_edges','max_removed','max_outside','status','seconds')}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--edges',type=int,default=196)
    p.add_argument('--removed',type=int,default=32)
    p.add_argument('--outside',type=int,default=34)
    p.add_argument('--seconds',type=float,default=120)
    p.add_argument('--control',action='store_true')
    p.add_argument('--output',type=Path,required=True)
    run(p.parse_args())
