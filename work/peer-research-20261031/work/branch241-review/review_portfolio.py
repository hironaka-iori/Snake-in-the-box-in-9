from pathlib import Path
import gzip,json,hashlib
from rup_check import check
from benchmark_portfolio import CONFIGS
H=Path(__file__).parent;O=H/'portfolio_results';rows=[]
for shape in ('0120','0123'):
 with gzip.open(H/f'alpha_rules_d{shape}/experiment.json.gz','rt') as f:d=json.load(f)
 cs=d['clauses'];prefix=d['proof'];basecheck=check(cs,prefix,require_empty=False);frozen=cs+[p['clause'] for p in prefix];digest=hashlib.sha256(json.dumps(cs,separators=(',',':')).encode()).hexdigest();tailrows=[]
 for name in CONFIGS:
  with gzip.open(O/f'{shape}_{name}.json.gz','rt') as f:t=json.load(f)
  assert t['summary']['source_CNF_sha256']==digest and t['summary']['frozen_prefix_steps']==len(prefix)
  ck=check(frozen,t['proof_tail'],require_empty=t['summary']['solver']['status']=='UNSAT');tailrows.append({'name':name,'checked':ck})
 with gzip.open(O/f'merged_{shape}.json.gz','rt') as f:m=json.load(f)
 assert m['clauses']==cs;checked=check(cs,m['proof'],require_empty=False)
 model=m.get('model')
 if model:
  a=set(model);assert all(any(l in a for l in c) for c in cs)
 rows.append({'shape':shape,'frozen_prefix':basecheck,'source_prefix_sha256':hashlib.sha256(json.dumps(prefix,separators=(',',':')).encode()).hexdigest(),'tails':tailrows,'merged_round':m.get('round'),'merged_complete':checked,'source_CNF_exactly_equal':True})
(O/'independent_review.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
