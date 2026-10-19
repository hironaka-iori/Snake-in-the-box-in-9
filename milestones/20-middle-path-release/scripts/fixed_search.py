"""Search around the paired 190-edge witness with both endpoints fixed."""
import argparse
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
sys.path.insert(0,str(ROOT/'milestones/19-coordinate-face-repair/scripts'))
from neighborhood_search import model
from exact_search import cp_model
from search_faces import sha

def run(args):
    source=HERE/'data/paired-seed190.json'
    path=json.loads(source.read_text())['path_vertices'];occupied=set(path)
    assert path[0]==41 and path[-1]==67
    m,x,starts,arcs=model(9,args.edges,path,args.removed)
    m.add(starts[41]==1);m.add(x[67]==1)
    m.add(sum(a for (v,w),a in arcs.items() if v==67)==0)
    for v,a in enumerate(starts):m.add_hint(a,int(v==41))
    used=set(zip(path,path[1:]))
    for edge,a in arcs.items():m.add_hint(a,int(edge in used))
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=args.seconds
    s.parameters.num_search_workers=2;s.parameters.random_seed=196
    status=s.solve(m)
    data={'source_sha256_lf':sha(source),'script_sha256_lf':sha(Path(__file__)),
          'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),
          'target_edges':args.edges,'removed_budget':args.removed,'fixed_endpoints':[41,67],
          'status':s.status_name(status),'seconds':s.wall_time,'branches':s.num_branches,'conflicts':s.num_conflicts,
          'scope':'Fixed endpoint pair, bounded deletion neighborhood; UNKNOWN is unresolved and INFEASIBLE is not a global Q9 bound.'}
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        result=[41]
        while True:
            nxt=[w for (v,w),a in arcs.items() if v==result[-1] and s.value(a)]
            if not nxt:break
            assert len(nxt)==1 and nxt[0] not in result
            result.append(nxt[0])
        assert len(result)==args.edges+1 and result[-1]==67
        for j,v in enumerate(result):
            for i,w in enumerate(result[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
        assert len(occupied-set(result))<=args.removed
        data.update(path_vertices=result,removed_vertices=sorted(occupied-set(result)),added_vertices=sorted(set(result)-occupied))
    args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:data[k] for k in ('target_edges','removed_budget','status','seconds')}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--edges',type=int,default=196)
    p.add_argument('--removed',type=int,default=64);p.add_argument('--seconds',type=float,default=120)
    p.add_argument('--output',type=Path,required=True);run(p.parse_args())
