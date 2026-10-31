"""Independent base/gate extraction and complete retained-proof review."""
import gzip,json,hashlib
from pathlib import Path
from alpha_rules_probe import rules,build
from rup_check import check
H=Path(__file__).resolve().parent;rows=[]
for shape in ('0120','0123'):
 folder=H/('alpha_rules_d'+shape)
 if not (folder/'experiment.json.gz').exists():continue
 with gzip.open(folder/'experiment.json.gz','rt') as f:d=json.load(f)
 E,_,_,_=build(d['meta']['path'],254);base=E.cnf.clauses[:]
 assert all(sum(w==21 for l,w in E.by_centre[x])==36 for x in E.centres)
 with gzip.open(H/f'loop_k3_cap254_r4_d{shape}_all8/static8.json.gz','rt') as f:manifest=json.load(f)
 base += [[-E.var[v] for v in c] for c in manifest['cycles'] if not set(c)&E.forbidden]
 additions=rules(E);assert d['clauses']==base+additions
 result=check(d['clauses'],d['proof'],require_empty=False)
 rows.append({'shape':shape,'clauses_rebuilt_exactly':True,'rule_clauses':len(additions),'full_proof':result,'status':'UNSAT' if result['empty_clause_checked'] else ('SAT' if d.get('model') else 'UNKNOWN')})
(H/'alpha_rules_independent_review.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
