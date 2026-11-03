"""Exact saved-cycle restrictions, with a small LP used only to select a candidate."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'work/solver_packages'),str(R/'work/share_packages')]
from ortools.linear_solver import pywraplp
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p1=H/'data/share18-impact/results.json';p2=R/'milestones/143-countfree-share13/data/range-analysis.json'
j=read(p1);profile=j['profiles'][0];cy=profile['cycle'];old=next(q for q in read(p2)['rows'] if q['floor']==18)
assert len(cy)==11 and all(e['v']==cy[(i+1)%11]['u'] for i,e in enumerate(cy))
def canon(xs):
 d={};out=[]
 for x in xs:
  if x not in d:d[x]=len(d)
  out.append(d[x])
 return tuple(out)
shapes=[min(canon(q['directions'][-6:]),canon(q['directions'][-6:][::-1])) for q in cy]
assert (0,1,2,0,3,4) not in shapes
weights=[q['weight'] for q in cy];events=[int(q['occurrence_event']) for q in cy]
assert sum(weights)==5399 and sum(events)==4 and all(q['countfree_012034_bonus']==0 for q in cy)
cycles=[(weights,events),(old['weights'],[0]*9)]
paths=[]
for cycle,(ws,es) in enumerate(cycles):
 for start in range(len(ws)):
  for length in range(1,len(ws)):
   indices=[(start+k)%len(ws) for k in range(length)]
   paths.append(dict(cycle=cycle,start=start,length=length,weight=sum(ws[k] for k in indices),events=sum(es[k] for k in indices)))
solver=pywraplp.Solver.CreateSolver('GLOP');assert solver
mu=solver.NumVar(0,solver.infinity(),'mean');credit=solver.NumVar(0,solver.infinity(),'credit');spread=solver.NumVar(0,solver.infinity(),'range')
for ws,es in cycles:solver.Add(len(ws)*mu<=sum(ws)+sum(es)*credit)
for p in paths:solver.Add(p['length']*mu-p['events']*credit-spread<=p['weight'])
solver.Maximize(227*mu-24*credit-spread)
assert solver.Solve()==pywraplp.Solver.OPTIMAL
M,C,Q=(F(v.solution_value()).limit_denominator(1000000) for v in [mu,credit,spread])
assert all(len(ws)*M<=sum(ws)+sum(es)*C for ws,es in cycles)
assert all(p['length']*M-p['events']*C-Q<=p['weight'] for p in paths)
active=[p for p in paths if p['length']*M-p['events']*C-Q==p['weight']]
zero=F(1098960*11+8*5399,4200*11+5399)
result=dict(status='PASS_EXACT_SAVED_CYCLE_RESTRICTIONS_AND_RATIONAL_CANDIDATE',cycle_weights=weights,
 cycle_events=events,cycle_shapes=[list(s) for s in shapes],cycle_edges=[q['edge'] for q in cy],
 cycle_total=5399,cycle_length=11,event_count=4,no_012034_windows=True,
 comparison=profile['comparison_bound'],zero_credit_zero_range_comparison=str(zero),zero_credit_gap=str(zero-235),
 arbitrary_012034_floor_obstruction='With zero occurrence credit and unchanged other weights and edges, the unaffected eleven-cycle forces mu<=5399/11. Even range0 gives comparison>=12131752/51599>235.',
 two_cycle_candidate=dict(mean=str(M),credit=str(C),range=str(Q),comparison=str((1098960+8*M+24*C+Q)/(4200+M)),
 gap_from235=str((1098960+8*M+24*C+Q)/(4200+M)-235),active_paths=active,
 exact_feasibility_checked=True,global_optimality_claim=False,scope='Exact rational feasible parameters for only two saved cycles and their proper subwalks. No full-graph potential or optimality claim.'),
 source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),p1,p2]})
out=H/'data/cycle-analysis.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','zero_credit_gap','two_cycle_candidate']}))
