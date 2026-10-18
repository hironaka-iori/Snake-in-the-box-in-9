"""Resynthesize one or two whole Q5 cells, preserving the rest of a seed."""
import argparse
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
from search import sha

def run(args):
    source=HERE/'data/aligned-seed.json'
    path=json.loads(source.read_text())['path_vertices'];occupied=set(path)
    regions=[[h] for h in range(16)] if args.cells==1 else [[h,k] for h,k in itertools.combinations(range(16),2) if (h^k).bit_count()==1]
    out={'target_edges':args.edges,'different_vertex_set':args.different,'cells_per_region':args.cells,'seconds_per_region':args.seconds,
         'source_sha256_lf':sha(source),'script_sha256_lf':sha(Path(__file__)),
         'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),
         'scope':'Only the released cells may change; no global exclusion is inferred from solver results.',
         'regions':[]}
    start=time.monotonic()
    for cells in regions:
        m,x,starts,arcs=model(9,args.edges,path,192)
        if args.different:m.add(sum(x[v] for v in occupied)<=len(occupied)-1)
        for v in range(512):
            if v>>5 not in cells:m.add(x[v]==int(v in occupied))
        s=cp_model.CpSolver();s.parameters.max_time_in_seconds=args.seconds
        s.parameters.num_search_workers=2;s.parameters.random_seed=196
        status=s.solve(m)
        row={'cells':cells,'status':s.status_name(status),'seconds':s.wall_time,
             'branches':s.num_branches,'conflicts':s.num_conflicts}
        if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
            result=[next(v for v,a in enumerate(starts) if s.value(a))]
            while True:
                nxt=[w for (v,w),a in arcs.items() if v==result[-1] and s.value(a)]
                if not nxt:break
                assert len(nxt)==1 and nxt[0] not in result
                result.append(nxt[0])
            assert len(result)==args.edges+1 and len(set(result))==len(result)
            for j,v in enumerate(result):
                for i,w in enumerate(result[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
            assert all(v>>5 in cells for v in set(result)^occupied)
            row['path_vertices']=result
        out['regions'].append(row)
        print(json.dumps(row if 'path_vertices' not in row else {'cells':cells,'status':row['status'],'edges':len(row['path_vertices'])-1}),flush=True)
        if 'path_vertices' in row:break
    out['elapsed_seconds']=time.monotonic()-start
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--cells',type=int,choices=[1,2],required=True)
    p.add_argument('--edges',type=int,default=192);p.add_argument('--seconds',type=float,default=3)
    p.add_argument('--different',action='store_true')
    p.add_argument('--output',type=Path,required=True)
    run(p.parse_args())
