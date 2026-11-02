"""Bounded local share tests on the four completed-profile sharp-cycle windows."""
from pathlib import Path
import argparse,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'milestones/28-direct-share-certificates/scripts'),str(ROOT/'work/solver_packages')]
from tagged_share import TaggedShare,Cadical153
from direct import census
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=15);ap.add_argument('--cap',type=int,default=16);ap.add_argument('--edge',type=int);args=ap.parse_args()
ds=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
profiles=read(ROOT/'milestones/109-relaxed-graph-test/data/restricted-profiles.json')
es=next(x for x in profiles['profiles'] if x['profile']=='completed')['sharp_cycle_original_indices']
if args.edge is not None:assert args.edge in es;es=[args.edge]
with np.load(ROOT/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz') as z:
    cases=[]
    for e in es:
        word=ds[int(z['direction'][e])][-6:];code=int(z['count_code'][e]);counts=[code//6**j%6+1 for j in range(4,-1,-1)]
        a,b=canon(word),canon(word[::-1]);reverse=b<a
        cases.append(dict(edge=e,directions=list(b if reverse else a),counts=counts[::-1] if reverse else counts,reverse=reverse))
pins={p.relative_to(ROOT).as_posix():sha(p) for p in [ROOT/'milestones/28-direct-share-certificates/scripts/tagged_share.py',
 ROOT/'milestones/28-direct-share-certificates/scripts/direct.py',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
 ROOT/'milestones/10-window-aggregate/scripts/wincert.py']}
folder=HERE/'data/share-probes';folder.mkdir(exist_ok=True)
for case in cases:
    path=folder/f'edge{case["edge"]}-cap{args.cap}.json';assert not path.exists(),'Preserve prior attempts; select a new cap or explicit new attempt.'
    bounds=[(6,21) if c==6 else (c,c) for c in case['counts']]
    begin=time.monotonic();enc=TaggedShare(case['directions'],bounds,args.cap);build_seconds=time.monotonic()-begin
    print(case['edge'],'encoded',enc.nv,'variables',len(enc.clauses),'clauses',round(build_seconds,3),'seconds',flush=True)
    start=time.monotonic();cuts=[];selected=None;report=None;status='UNKNOWN';calls=0
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-start<args.seconds:
            solver.conf_budget(1000);ok=solver.solve_limited();calls+=1
            if ok is None:continue
            if not ok:status='UNSAT_UNCERTIFIED';break
            model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0}
            report=census(S,9,enc.window[1:-1]);report.pop('degree')
            assert all(lo<=a<=hi for a,(lo,hi) in zip(report['alpha'],bounds))
            assert report['total_share']<=args.cap
            if not report['cycles']:status='SAT_LOCAL_WITNESS';selected=sorted(S);break
            for cycle in report['cycles']:
                cuts.append(cycle);solver.add_clause([-enc.var[v] for v in cycle])
    assert all(sha(ROOT/p)==h for p,h in pins.items())
    out=dict(case,cap=args.cap,bounds=bounds,status=status,selected=selected,census=report,cycle_cuts=cuts,
        variables=enc.nv,clauses=len(enc.clauses),build_seconds=build_seconds,solver_seconds=time.monotonic()-start,
        conflict_budget_per_call=1000,solve_calls=calls,nominal_time_budget=args.seconds,
        source_files_sha256=pins,script_sha256=sha(Path(__file__)),
        scope='Local computational probe only. UNSAT requires a fresh certificate and checked semantics before becoming a share theorem. A SAT assignment is a local witness, not a long snake or periodic realization. Conflict budgets bound calls; nominal time is checked between calls.')
    path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(case['edge'],status,'share',report['total_share'] if selected else None,'seconds',round(out['solver_seconds'],3),flush=True)
