"""Merge the current path and chosen cycles while preserving the other cycles."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work'))
sys.path.insert(0,str(ROOT/'milestones/14-component-construction/scripts'))
from neighborhood_search import model
from exact_search import cp_model
from check_snake import verify
from component_search import components


def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def run(args):
    data=json.loads(args.source.read_text(encoding='utf-8'))
    selected=set(data['seed_vertices'])
    parts,adj=components(selected,9)
    ends={v for v in selected if len(adj[v])==1}
    assert len(selected)==197 and len(ends)==2 and all(len(adj[v]) in (1,2)for v in selected)
    pathpart=next(c for c in parts if set(c)&ends)
    cycles=[c for c in parts if c!=pathpart]
    released={int(i)for i in args.cycles.split(',') if i!=''}
    assert released<=set(range(len(cycles)))
    frozen={v for i,c in enumerate(cycles)if i not in released for v in c}
    forbidden=frozen | {v^(1<<k)for v in frozen for k in range(9)}
    free_seed=sorted(selected-frozen)
    target=len(free_seed)-1
    m,x,starts,arcs=model(9,target,free_seed,len(free_seed))
    for v in forbidden:m.add(x[v]==0)
    release_path={int(v)for v in args.release_path_vertices.split(',')if v!=''}
    assert release_path<=set(pathpart) and (args.keep_path or not release_path)
    retained_path=set(pathpart)-release_path if args.keep_path else set()
    for v in retained_path:m.add(x[v]==1)
    if args.max_removed is not None:
        m.add(sum(x[v]for v in free_seed)>=len(free_seed)-args.max_removed)
    cuts=data.get('cuts_to_retain',[])
    for c in cuts:
        assert len(set(c))==len(c) and c
        assert all(sum((v^w).bit_count()==1 for w in c)==2 for v in c)
        m.add(sum(x[v]for v in c if v not in frozen)<=len(c)-1-len(set(c)&frozen))
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=args.seconds
    solver.parameters.num_search_workers=args.workers
    solver.parameters.random_seed=args.seed
    begin=time.monotonic();status=solver.solve(m)
    report={'source':args.source.relative_to(ROOT).as_posix(),'source_sha256_lf':sha(args.source),
        'released_cycle_indices':sorted(released),'frozen_vertices':sorted(frozen),
        'allowed_vertices':512-len(forbidden),'target_path_edges':target,
        'keep_original_path':args.keep_path,'max_removed':args.max_removed,
        'retained_path_vertices':sorted(retained_path),'released_path_vertices':sorted(release_path),
        'both_endpoints_free':True,'retained_cuts':cuts,'seed':args.seed,'workers':args.workers,
        'status':solver.status_name(status),'seconds':time.monotonic()-begin,
        'branches':solver.num_branches,'conflicts':solver.num_conflicts,
        'scope':'Restricted merger with the recorded cycles frozen; no global impossibility claim.'}
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        path=[next(v for v,a in enumerate(starts)if solver.value(a))]
        while True:
            following=[w for (v,w),a in arcs.items()if v==path[-1]and solver.value(a)]
            if not following:break
            assert len(following)==1 and following[0]not in path
            path.append(following[0])
        checked=verify([(a^b).bit_length()-1 for a,b in zip(path,path[1:])],9)
        assert checked['edges']==target and checked['vertex_sequence']==[v^path[0]for v in path]
        assert not set(path)&forbidden
        result=frozen|set(path)
        newparts,newadj=components(result,9)
        assert len(result)==197 and len(newparts)==len(cycles)-len(released)+1
        assert all(not set(c)<=result for c in cuts)
        report.update(path_vertices=path,seed_vertices=sorted(result),components=newparts,
            cuts_to_retain=cuts,pairs_checked=checked['pairs_checked'],
            removed_vertices=sorted(selected-result),added_vertices=sorted(result-selected))
        if len(newparts)==1:report['status']='INDEPENDENTLY_CHECKED_196_EDGE_WITNESS'
    report['script_sha256_lf']=sha(Path(__file__))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:report[k]for k in ('status','target_path_edges','allowed_vertices','seconds','branches','conflicts')}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--source',type=Path,default=ROOT/'milestones/14-component-construction/data/improved-seed.json')
    p.add_argument('--cycles',default='0')
    p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--seed',type=int,default=196)
    p.add_argument('--keep-path',action='store_true')
    p.add_argument('--release-path-vertices',default='')
    p.add_argument('--max-removed',type=int)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.source=a.source.resolve();run(a)
