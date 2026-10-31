"""Bounded actual queries with the reviewed guarded cut; no Lean bridge claim."""
from pathlib import Path
import sys,gzip,json,hashlib,time
from cutset_cnf import build,add_cut
from alpha_rules_probe import rules
from solver_reduced import Solver
from rup_check import check
from research_loop import save
H=Path(__file__).resolve().parent;R=H.parent/'branch241-review';O=H/'cut_probes';O.mkdir(exist_ok=True)
for shape in ['0120','0123']:
 source=R/f'portfolio_results/merged_{shape}.json.gz'
 with gzip.open(source,'rt') as f:d=json.load(f)
 E,g,m,meta=build(d['meta']['path'],254);rules(E);before=len(E.cnf.clauses);U={v for v in range(512) if (v^2).bit_count()<=2};cut=add_cut(E,g,m,U,E.centres[0]);new=E.cnf.clauses[before:]
 n=len(d['clauses']);delta=len(new);cs=d['clauses']+new;prefix=[{'clause':p['clause'],'hints':[i if i<=n else i+delta for i in p['hints']]} for p in d['proof']]
 S=Solver(cs,prefix,nvars=E.cnf.nv,primary=E.var.values(),phase_true=d.get('phase_true',[]),restart='luby',seed=101);r=S.solve(seconds=15);model=r.pop('model',None);checked=check(cs+[p['clause'] for p in prefix],S.proof,require_empty=r['status']=='UNSAT')
 if model:
  selected=set(model);assert all(any(l in selected for l in c) for c in cs)
 row={'shape':shape,'status':r['status'],'solver':r,'cut':cut,'shifted_prefix_checked':S.prefix_check,'tail_checked':checked,'source_checkpoint_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'old_static_clause_count':n,'new_static_clause_count':len(cs),'Lean_checked':False,'new_upper_bound':None}
 save(O/f'{shape}.json.gz',{'summary':row,'added_static_clauses':new,'proof_tail':S.proof,'model':model});(O/f'{shape}_summary.json').write_text(json.dumps(row,indent=2));print(json.dumps(row),flush=True)
