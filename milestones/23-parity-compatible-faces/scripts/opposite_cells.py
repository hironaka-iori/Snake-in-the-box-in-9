"""Replace two opposite Q5 cells; their union varies all nine coordinates."""
import argparse,itertools,json,sys,time
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
sys.path.insert(0,str(ROOT/'milestones/19-coordinate-face-repair/scripts'))
from neighborhood_search import model
from exact_search import cp_model
from search_faces import sha
def check(p):
    assert len(set(p))==len(p)
    for j,v in enumerate(p):
        for i,w in enumerate(p[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
def regions():
    for free in itertools.combinations(range(9),5):
        fixed=[k for k in range(9) if k not in free];mask=sum(1<<k for k in fixed)
        for bits in range(8):
            value=sum(((bits>>j)&1)<<k for j,k in enumerate(fixed))
            yield {'free_coordinates':list(free),'fixed_mask':mask,'values':[value,value^mask]}
def run(args):
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    p=json.loads(source.read_text())['path_vertices'];check(p);occupied=set(p)
    base,x,starts,arcs=model(9,args.edges,p,len(p));begin=time.monotonic()
    report={'script_sha256_lf':sha(Path(__file__)),'source_sha256_lf':sha(source),'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),'target_edges':args.edges,'seconds_per_region':args.seconds,'total_seconds_limit':args.total,'total_regions':1008,'regions':[],'scope':'Outside the union of two opposite Q5 cells, all selected and unselected vertices are fixed. Restricted solver results; no global or Lean exclusion.'}
    for index,r in enumerate(regions()):
        if time.monotonic()-begin>=args.total:break
        inside={v for v in range(512) if v&r['fixed_mask'] in r['values']}
        assert len(inside)==64
        m=base.clone()
        for v in range(512):
            if v not in inside:m.add(x[v]==int(v in occupied))
        s=cp_model.CpSolver();s.parameters.max_time_in_seconds=min(args.seconds,max(.001,args.total-(time.monotonic()-begin)))
        s.parameters.num_search_workers=2;s.parameters.random_seed=193
        status=s.solve(m);row={**r,'index':index,'selected_inside':len(inside&occupied),'endpoints_inside':sum(v in inside for v in (p[0],p[-1])),'status':s.status_name(status),'seconds':s.wall_time,'branches':s.num_branches,'conflicts':s.num_conflicts}
        if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
            q=[next(v for v,t in enumerate(starts) if s.value(t))]
            while True:
                nxt=[w for (v,w),t in arcs.items() if v==q[-1] and s.value(t)]
                if not nxt:break
                assert len(nxt)==1 and nxt[0] not in q;q+=nxt
            check(q);assert len(q)==args.edges+1 and set(q)^occupied<=inside
            row['path_vertices']=q
        report['regions'].append(row)
        if index%64==63 or 'path_vertices' in row:
            print(json.dumps({'regions':index+1,'statuses':dict(Counter(v['status'] for v in report['regions']))}),flush=True)
        report.update(status_counts=dict(Counter(v['status'] for v in report['regions'])),elapsed_seconds=time.monotonic()-begin,complete=len(report['regions'])==1008)
        args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        if 'path_vertices' in row:break
    print(json.dumps({'regions':len(report['regions']),'statuses':report['status_counts'],'complete':report['complete'],'seconds':report['elapsed_seconds']}),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--edges',type=int,default=193);ap.add_argument('--seconds',type=float,default=1);ap.add_argument('--total',type=float,default=180);ap.add_argument('--output',type=Path,required=True);run(ap.parse_args())
