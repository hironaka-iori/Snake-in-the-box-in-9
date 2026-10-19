"""Repeated coordinate-face replacements, rebuilding after each accepted gain."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
sys.path.insert(0,str(ROOT/'milestones/19-coordinate-face-repair/scripts'))
from neighborhood_search import model
from exact_search import cp_model
from search_faces import faces,sha

def check(path):
    assert len(path)==len(set(path))
    for j,v in enumerate(path):
        for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)

def run(args):
    source=ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json'
    path=json.loads(source.read_text())['path_vertices'];check(path)
    middle=json.loads((ROOT/'milestones/19-coordinate-face-repair/data/two-arm-growth.json').read_text())['fixed_path']
    candidates=faces(args.dimension)
    # Prioritize faces that cross both coordinates formerly defining the
    # free face; no candidate is removed by this ordering.
    candidates.sort(key=lambda f:(-len(set(f['free_coordinates'])&{7,8}),f['fixed_mask'],f['fixed_value']))
    report={'source_sha256_lf':sha(source),'script_sha256_lf':sha(Path(__file__)),
            'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),
            'face_driver_sha256_lf':sha(ROOT/'milestones/19-coordinate-face-repair/scripts/search_faces.py'),
            'dimension':args.dimension,'target_edges':196,'total_seconds':args.seconds,
            'seconds_per_face':args.per_face,'initial_path':path,'passes':[],
            'scope':'Constructive local growth from a 186-edge seed. Failure to improve is restricted to visited regions and time limits.'}
    begin=time.monotonic();args.output.parent.mkdir(parents=True,exist_ok=True)
    while len(path)<197 and time.monotonic()-begin<args.seconds:
        occupied=set(path);target=len(path)
        base,x,starts,arcs=model(9,target,path,len(path))
        current={'starting_edges':len(path)-1,'target_edges':target,'trials':[]};report['passes'].append(current)
        improved=False
        for index,face in enumerate(candidates):
            remaining=args.seconds-(time.monotonic()-begin)
            if remaining<=0:break
            inside={v for v in range(512) if v&face['fixed_mask']==face['fixed_value']}
            m=base.clone()
            for v in range(512):
                if v not in inside:m.add(x[v]==int(v in occupied))
            solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=min(args.per_face,remaining)
            solver.parameters.num_search_workers=2;solver.parameters.random_seed=196+len(report['passes'])
            status=solver.solve(m)
            row={**face,'status':solver.status_name(status),'seconds':solver.wall_time}
            current['trials'].append(row)
            if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
                new=[next(v for v,a in enumerate(starts) if solver.value(a))]
                while True:
                    following=[w for (v,w),a in arcs.items() if v==new[-1] and solver.value(a)]
                    if not following:break
                    assert len(following)==1 and following[0] not in new
                    new.append(following[0])
                check(new);assert len(new)==target+1 and (set(new)^occupied)<=inside
                current.update(path_vertices=new,removed_vertices=sorted(occupied-set(new)),
                               added_vertices=sorted(set(new)-occupied),original_middle_removed=sorted(set(middle)-set(new)))
                path=new;improved=True
                print(json.dumps({'improved_edges':len(path)-1,'trials':len(current['trials']),
                                  'original_middle_removed':len(current['original_middle_removed'])}),flush=True)
                break
            if (index+1)%32==0:
                print(json.dumps({'target':target,'trials':index+1,'statuses':dict(Counter(r['status'] for r in current['trials']))}),flush=True)
        report.update(best_edges=len(path)-1,path_vertices=path,elapsed_seconds=time.monotonic()-begin)
        args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        if not improved:break
    print(json.dumps({'best_edges':len(path)-1,'passes':len(report['passes']),'seconds':time.monotonic()-begin}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--dimension',type=int,default=6)
    p.add_argument('--seconds',type=float,default=120);p.add_argument('--per-face',type=float,default=1)
    p.add_argument('--output',type=Path,required=True);run(p.parse_args())
