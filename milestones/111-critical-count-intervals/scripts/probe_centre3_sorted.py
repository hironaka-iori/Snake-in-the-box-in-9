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
cases=[dict(name=f'centre{centre}-sum{limit}-sorted',directions=[0,1,2,3,4,0],bounds=[[0,21],[0,21],[0,centre],[0,21],[0,21]],outer_sum_cap=limit,purpose='Test sum of four outer counts at a higher middle-count cap.') for centre,limit in [(3,18)]]
pins={p.relative_to(ROOT).as_posix():sha(p) for p in [ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
 ROOT/'milestones/10-window-aggregate/scripts/wincert.py',ROOT/'milestones/28-direct-share-certificates/scripts/direct.py',
 ROOT/'milestones/110-critical-cycle-core-screen/data/count-profiles-all/results.json',ROOT/'milestones/59-extended-share-window/extended/data/model.json']}
if args.case:cases=[c for c in cases if c['name']==args.case];assert cases
for c in cases:
    path=HERE/'data/probes'/(c['name']+'.json')
    assert not path.exists(),'Keep prior attempts immutable'
    t=time.monotonic();enc=TaggedEncoding(window(c['directions']),[tuple(b) for b in c['bounds']],radius=4);build=time.monotonic()-t
    from itertools import combinations
    lits=[]
    for i in [1,2,4,5]:
        v=enc.window[i];used={v^enc.window[i-1],v^enc.window[i+1]}
        lits += [-enc.var[v^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
    assert len(lits)==84
    lits.sort()
    enc.atmost(lits,c['outer_sum_cap'],('unproved_sum',))
    start=time.monotonic();cuts=[];status='UNKNOWN';calls=0;S=None;report=None
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-start<args.seconds:
            solver.conf_budget(1000);result=solver.solve_limited();calls+=1
            if result is None:continue
            if not result:status='UNSAT_UNCERTIFIED';break
            model=solver.get_model();selected={v for v in enc.ball if model[enc.var[v]-1]>0}
            report=census(selected,9,enc.window[1:-1]);report.pop('degree')
            assert all(lo<=v<=hi for v,(lo,hi) in zip(report['alpha'],c['bounds']))
            assert sum(report['alpha'][i] for i in [0,1,3,4])<=c['outer_sum_cap']
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
