"""Equal-budget real-query reduction test. Separate immutable proof tails."""
from pathlib import Path
import gzip,json,time
from solver_plus import Solver as Full
from solver_reduced import Solver as Reduced
from rup_check import check
from research_loop import save
H=Path(__file__).resolve().parent;O=H/'portfolio_results';D=H/'reduction_probe';D.mkdir(exist_ok=True)
with gzip.open(O/'merged_0120.json.gz','rt') as f:d=json.load(f)
cs=d['clauses'];prefix=d['proof'];check(cs,prefix,require_empty=False);base=cs+[p['clause'] for p in prefix]
from alpha_rules_probe import build
E,_,_,_=build(d['meta']['path'],254);rows=[]
for name in ['full','reduced']:
 start=time.perf_counter();kw=dict(primary=E.var.values(),phase_true=d.get('phase_true',[]),restart='luby',seed=68)
 S=Full(base,**kw) if name=='full' else Reduced(cs,prefix,**kw)
 prep=time.perf_counter()-start;r=S.solve(seconds=20);model=r.pop('model',None);v=check(base,S.proof,require_empty=r['status']=='UNSAT')
 if model:
  assigned=set(model);assert all(any(l in assigned for l in c) for c in base)
 audit=getattr(S,'deactivation_audit',[])
 for a in audit:assert all(i>=len(cs) and len(S.clauses[i])>2 and i not in a['locked_at_reduction'] and i not in a['excluded'] for i in a['ids_zero_based'])
 row={'configuration':name,'solver':r,'constructor_and_prefixcheck_seconds':prep,'new_RUP':v,'frozen_prefix_steps':len(prefix),'total_wall_before_save':time.perf_counter()-start}
 save(D/f'{name}.json.gz',{'summary':row,'proof_tail':S.proof,'model':model,'deactivation_audit':audit});rows.append(row);(D/'summary.json').write_text(json.dumps(rows,indent=2));print(json.dumps(row),flush=True)
