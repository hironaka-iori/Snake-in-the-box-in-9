"""Bounded arbitrary-length count-window probes, preserving all interval values."""
from pathlib import Path
import argparse,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'milestones/28-direct-share-certificates/scripts'),str(R/'work/solver_packages')]
from tagged_share import TaggedEncoding,Cadical153
from direct import window,census
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--input',default='data/cases-initial.json');ap.add_argument('--seconds',type=float,default=30);args=ap.parse_args()
source=H/args.input;cases=read(source)
for case in cases:
    p=H/'data/probes'/(case['name']+'.json');assert not p.exists()
    assert len(case['bounds'])==len(case['directions'])-1 and case.get('sum_cap') is None
    pins={x.relative_to(R).as_posix():sha(x) for x in [source,R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',R/'milestones/10-window-aggregate/scripts/wincert.py',R/'milestones/28-direct-share-certificates/scripts/tagged_share.py',R/'milestones/28-direct-share-certificates/scripts/direct.py']}
    if 'source' in case:assert sha(R/case['source'])==case['source_sha256'];pins[case['source']]=case['source_sha256']
    start=time.monotonic();enc=TaggedEncoding(window(case['directions']),[tuple(b) for b in case['bounds']],radius=case['radius'])
    if case['radius']==9:assert set(enc.ball)==set(range(512))
    build=time.monotonic()-start;start=time.monotonic();cuts=[];calls=0;selected=report=None;status='UNKNOWN'
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-start<args.seconds:
            solver.conf_budget(1000);result=solver.solve_limited();calls+=1
            if result is None:continue
            if not result:status='UNSAT_UNCERTIFIED';break
            model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};report=census(S,9,enc.window[1:-1]);report.pop('degree')
            assert all(lo<=v<=hi for v,(lo,hi) in zip(report['alpha'],case['bounds']))
            if not report['cycles']:selected=sorted(S);status='SAT_PATH_CANDIDATE' if case['radius']==9 else 'SAT_LOCAL_CANDIDATE';break
            for cut in report['cycles']:
                assert cut and len(cut)==len(set(cut))
                assert all(sum((v^(1<<k)) in set(cut) for k in range(9))>=2 for v in cut)
                cuts.append(cut);solver.add_clause([-enc.var[v] for v in cut])
    assert all(sha(R/k)==v for k,v in pins.items())
    out=dict(case,status=status,selected=selected,census=report,cycle_cuts=cuts,window=enc.window,ball_vertices=len(enc.ball),variables=enc.nv,clauses=len(enc.clauses),sum_counter_added=False,build_seconds=build,solver_seconds=time.monotonic()-start,nominal_seconds=args.seconds,conflict_budget_per_call=1000,calls=calls,source_files_sha256=pins,script_sha256=sha(Path(__file__)),scope='Native count-window evidence with full stated intervals and no sum cap. Positive paths require independent verification; negative answers require checked certificates. No global extremal bound.')
    p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(case['name'],status,'alpha',None if report is None else report['alpha'],'cuts',len(cuts),'seconds',round(out['solver_seconds'],3),flush=True)
