"""Same frozen CNF/prefix, equal solve budgets; check every generated proof tail.
Experimental measurements, no universal speedup or improved upper bound claim.
"""
from pathlib import Path
import argparse,gzip,json,time,gc,hashlib
from solver import Solver as Original
from solver_plus import Solver as Enhanced
from rup_check import check
from research_loop import save
H=Path(__file__).resolve().parent
CONFIGS={'baseline':None,'binary_geometric':{'restart':'geometric'},'binary_lbd':{'restart':'lbd'},'binary_luby':{'restart':'luby'},'circular_lbd':{'restart':'lbd','circular':True},'minimize_lbd':{'restart':'lbd','minimize':True}}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=6);ap.add_argument('--shapes',nargs='+',default=['0120','0123']);a=ap.parse_args();out=H/'portfolio_results';out.mkdir(exist_ok=True);rows=[]
 for shape in a.shapes:
  with gzip.open(H/f'alpha_rules_d{shape}/experiment.json.gz','rt') as f:d=json.load(f)
  cs=d['clauses'];prefix=d['proof'];check(cs,prefix,require_empty=False);frozen=cs+[p['clause'] for p in prefix]
  from alpha_rules_probe import build
  E,_,_,_=build(d['meta']['path'],254)
  for name,kw in CONFIGS.items():
   t=time.perf_counter();S=(Original if kw is None else Enhanced)(frozen,max(abs(l) for c in cs for l in c),primary=E.var.values(),phase_true=d.get('phase_true',E.var.values()),**(kw or {}));init=time.perf_counter()-t
   r=S.solve(seconds=a.seconds);model=r.pop('model',None);checked=check(frozen,S.proof,require_empty=r['status']=='UNSAT')
   if model:
    assignment=set(model);assert all(any(l in assignment for l in c) for c in frozen)
    from charge_fast import Charges,Geometry
    selected=[v for v,x in E.var.items() if x in assignment];q=Charges(Geometry(9),selected).cheap()['r6plus']['values'];assert sum(q[v] for v in E.centres)<=254
   item={'shape':shape,'configuration':name,'solve_budget_seconds':a.seconds,'constructor_seconds':init,'solver':r,'RUP_checked':checked,'source_CNF_sha256':hashlib.sha256(json.dumps(cs,separators=(',',':')).encode()).hexdigest(),'frozen_prefix_sha256':hashlib.sha256(json.dumps(prefix,separators=(',',':')).encode()).hexdigest(),'frozen_prefix_steps':len(prefix),'wall_seconds_before_save':time.perf_counter()-t}
   save(out/f'{shape}_{name}.json.gz',{'summary':item,'proof_tail':S.proof,'model':model});rows.append(item);(out/'summary.json').write_text(json.dumps(rows,indent=2));print(json.dumps(item),flush=True);del S;gc.collect()
if __name__=='__main__':main()
