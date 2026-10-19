"""Replace a coordinate face while preserving every vertex outside it.

The model is cloned from the established full-cube induced-path model.
Checkpointed face outcomes are bounded solver results, not global proofs.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
from neighborhood_search import model
from exact_search import cp_model

def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()

def faces(d):
    result=[]
    for free in itertools.combinations(range(9),d):
        fixed=[k for k in range(9) if k not in free]
        mask=sum(1<<k for k in fixed)
        for bits in range(1<<len(fixed)):
            value=sum(((bits>>j)&1)<<k for j,k in enumerate(fixed))
            result.append({'free_coordinates':list(free),'fixed_mask':mask,'fixed_value':value})
    return result

def run(args):
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    path=json.loads(source.read_text())['path_vertices'];occupied=set(path)
    base,x,starts,arcs=model(9,args.edges,path,len(path))
    candidates=faces(args.dimension)
    if args.limit:candidates=candidates[:args.limit]
    report={'dimension':args.dimension,'target_edges':args.edges,'seconds_per_face':args.seconds,
            'requested_faces':len(candidates),'source_sha256_lf':sha(source),
            'script_sha256_lf':sha(Path(__file__)),'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),
            'scope':'The selected and unselected vertices outside each face are fixed. No solver result is a global Q9 bound.',
            'faces':[]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    begin=time.monotonic()
    for index,face in enumerate(candidates):
        inside={v for v in range(512) if v&face['fixed_mask']==face['fixed_value']}
        assert len(inside)==1<<args.dimension
        m=base.clone()
        for v in range(512):
            if v not in inside:m.add(x[v]==int(v in occupied))
        solver=cp_model.CpSolver()
        solver.parameters.max_time_in_seconds=args.seconds
        solver.parameters.num_search_workers=2
        solver.parameters.random_seed=196
        status=solver.solve(m)
        row={**face,'index':index,'selected_inside':len(inside&occupied),
             'endpoints_inside':sum(v in inside for v in [path[0],path[-1]]),
             'status':solver.status_name(status),'seconds':solver.wall_time,
             'branches':solver.num_branches,'conflicts':solver.num_conflicts}
        if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
            result=[next(v for v,a in enumerate(starts) if solver.value(a))]
            while True:
                following=[w for (v,w),a in arcs.items() if v==result[-1] and solver.value(a)]
                if not following:break
                assert len(following)==1 and following[0] not in result
                result.append(following[0])
            assert len(result)==args.edges+1 and len(set(result))==len(result)
            for j,v in enumerate(result):
                for i,w in enumerate(result[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
            assert set(result)^occupied<=inside
            row['path_vertices']=result
        report['faces'].append(row)
        if (index+1)%16==0 or 'path_vertices' in row or index+1==len(candidates):
            report['elapsed_seconds']=time.monotonic()-begin
            report['status_counts']=dict(Counter(r['status'] for r in report['faces']))
            args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
            print(json.dumps({'faces':index+1,'total':len(candidates),'status_counts':report['status_counts']}),flush=True)
        if 'path_vertices' in row:break

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--dimension',type=int,default=6)
    p.add_argument('--edges',type=int,default=196);p.add_argument('--seconds',type=float,default=1)
    p.add_argument('--limit',type=int,default=0);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();assert 1<=args.dimension<=9
    run(args)
