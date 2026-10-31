"""Continue merged proof with a seeded Luby strategy; all state reconstructed."""
from pathlib import Path
import argparse,gzip,json,time
from solver_plus import Solver
from solver import Solver as Original
from solver_reduced import Solver as Reduced
from benchmark_portfolio import CONFIGS
from rup_check import check
from research_loop import save
from alpha_rules_probe import build
H=Path(__file__).resolve().parent;O=H/'portfolio_results'
def run(shape,seconds,configuration="auto",reduced=False):
 path=O/f'merged_{shape}.json.gz'
 with gzip.open(path,'rt') as f:d=json.load(f)
 cs=d['clauses'];proof=d['proof'];prefix_check=check(cs,proof,require_empty=False)
 if proof and proof[-1]['clause']==[]:print('already UNSAT');return
 if d.get('model'):print('saved SAT model needs geometric analysis; search stopped');return
 E,_,_,_=build(d['meta']['path'],254);round=d.get('round',0)+1
 if configuration=='auto':
  rows=json.loads((O/'summary.json').read_text());configuration=max((r for r in rows if r['shape']==shape),key=lambda r:r['solver']['conflicts']/r['solver']['seconds'])['configuration']
 options=CONFIGS[configuration]
 kw=dict(primary=E.var.values(),phase_true=d.get('phase_true',[]),**({} if options is None else dict(options,seed=17*round)))
 if reduced:
  if options is None:kw.update(binary=False,restart='geometric')
  S=Reduced(cs,proof,**kw);configuration+=' + search reduction'
 else:S=(Original if options is None else Solver)(cs+[p['clause'] for p in proof],**kw)
 r=S.solve(seconds=seconds);model=r.pop('model',None);checked=check(cs+[p['clause'] for p in proof],S.proof,require_empty=r['status']=='UNSAT')
 if model:
  assigned=set(model);assert all(any(l in assigned for l in c) for c in cs)
  from charge_fast import Charges,Geometry
  from geometry_check import components
  selected=[v for v,x in E.var.items() if x in assigned];q=Charges(Geometry(9),selected).cheap()['r6plus']['values'];score=sum(q[v] for v in E.centres);assert score<=254
  d['decoded_model']={'selected':selected,'score':score,'components':components(selected),'scope':'local relaxation; not yet a global snake'}
 d['proof']+=S.proof;d['checked']={'RUP_steps_checked':len(d['proof']),'unit_hints_checked':prefix_check['unit_hints_checked']+checked['unit_hints_checked'],'empty_clause_checked':r['status']=='UNSAT'};d['phase_true']=[v for v in range(1,S.n+1) if S.phase[v]>0];d['round']=round;d['model']=model;d['last']={'configuration':configuration,'selection_caveat':'short pilot conflict rate, not a proven solving-time optimum','solver':r,'new_checked':checked,'total_steps':len(d['proof'])};d.setdefault('history',[]).append({'round':round,**d['last']});save(path,d);(O/f'continued_{shape}.json').write_text(json.dumps(d['last'],indent=2));print(json.dumps({'shape':shape,**d['last']}),flush=True)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--seconds',type=float,default=15);a.add_argument('--reduced',action='store_true');a.add_argument('--configuration',choices=['auto']+list(CONFIGS),default='auto');a.add_argument('--shape',choices=['0120','0123'],required=True);x=a.parse_args();run(x.shape,x.seconds,x.configuration,x.reduced)
