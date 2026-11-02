"""Bounded local probes for relaxed intervals and exact-six critical windows."""
from pathlib import Path
import argparse,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'milestones/28-direct-share-certificates/scripts'),str(ROOT/'work/solver_packages')]
from tagged_share import TaggedEncoding,Cadical153
from direct import window,census
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in ['data/probes','audit','logs','upstream']:(HERE/d).mkdir(parents=True,exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--case');ap.add_argument('--seconds',type=float,default=12);args=ap.parse_args()
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
ds=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
prior=read(ROOT/'milestones/110-critical-cycle-core-screen/data/count-profiles-all/results.json')
cases=[]
for profile in prior['profiles']:
    for row in profile['cycle']:
        w=ds[row['direction']][-6:];f,b=canon(w),canon(w[::-1]);xs=[row['count_code']//6**j%6+1 for j in range(4,-1,-1)]
        if b<f:w=list(b);xs=xs[::-1]
        else:w=list(f)
        cases.append(dict(name=f'exact-edge{row["edge"]}',directions=w,bounds=[[x,x] for x in xs],
            original_symbols=xs,profile=profile['profile'],edge=row['edge'],purpose='Replace symbol6 by exact count6; a hypothetical excess test, not a full interval exclusion.'))
for name,bounds in [
 ('relaxed-used-core',[[0,5],[0,5],[2,2],[0,4],[0,5]]),
 ('symmetric-upper5',[[0,5],[0,5],[2,2],[0,5],[0,5]]),
 ('critical-upper6',[[0,6],[0,3],[2,2],[0,5],[0,6]]),
 ('critical-upper21',[[0,21],[0,3],[2,2],[0,5],[0,21]])]:
    cases.append(dict(name=name,directions=[0,1,2,3,4,0],bounds=bounds,purpose='Candidate interval relaxation on the checked direction shape.'))
pins={p.relative_to(ROOT).as_posix():sha(p) for p in [ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
 ROOT/'milestones/10-window-aggregate/scripts/wincert.py',ROOT/'milestones/28-direct-share-certificates/scripts/direct.py',
 ROOT/'milestones/110-critical-cycle-core-screen/data/count-profiles-all/results.json',ROOT/'milestones/59-extended-share-window/extended/data/model.json']}
if args.case:cases=[c for c in cases if c['name']==args.case];assert cases
for c in cases:
    path=HERE/'data/probes'/(c['name']+'.json')
    assert not path.exists(),'Keep prior attempts immutable'
    t=time.monotonic();enc=TaggedEncoding(window(c['directions']),[tuple(b) for b in c['bounds']],radius=4);build=time.monotonic()-t
    start=time.monotonic();cuts=[];status='UNKNOWN';calls=0;S=None;report=None
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-start<args.seconds:
            solver.conf_budget(1000);result=solver.solve_limited();calls+=1
            if result is None:continue
            if not result:status='UNSAT_UNCERTIFIED';break
            model=solver.get_model();selected={v for v in enc.ball if model[enc.var[v]-1]>0}
            report=census(selected,9,enc.window[1:-1]);report.pop('degree')
            assert all(lo<=v<=hi for v,(lo,hi) in zip(report['alpha'],c['bounds']))
            if not report['cycles']:S=sorted(selected);status='SAT_LOCAL_WITNESS';break
            for cut in report['cycles']:
                assert all(sum((v^(1<<j)) in set(cut) for j in range(9))>=2 for v in cut)
                cuts.append(cut);solver.add_clause([-enc.var[v] for v in cut])
    assert all(sha(ROOT/p)==h for p,h in pins.items())
    out=dict(c,status=status,selected=S,census=report,cycle_cuts=cuts,variables=enc.nv,clauses=len(enc.clauses),
        build_seconds=build,solver_seconds=time.monotonic()-start,nominal_seconds=args.seconds,conflict_budget_per_call=1000,calls=calls,
        source_files_sha256=pins,script_sha256=sha(Path(__file__)),scope='Bounded native local-model evidence. Exact6 is stricter than graph symbol6. No theorem, whole-snake witness or global bound follows from this probe alone.')
    path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(c['name'],status,'cuts',len(cuts),'seconds',round(out['solver_seconds'],3),flush=True)
