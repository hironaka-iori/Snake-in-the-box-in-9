from pathlib import Path
import sys,gzip,json,hashlib
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H.parent/'branch241-review'))
from rup_check import check
from cutset_cnf import build,add_cut
from alpha_rules_probe import rules
for shape in ['0120','0123']:
 source=H.parent/f'branch241-review/portfolio_results/merged_{shape}.json.gz'
 with gzip.open(H/f'cut_probes/{shape}.json.gz','rt') as f:t=json.load(f)
 assert hashlib.sha256(source.read_bytes()).hexdigest()==t['summary']['source_checkpoint_sha256'],'restore matching extended-run checkpoint before verification'
 with gzip.open(source,'rt') as f:d=json.load(f)
 E,g,m,_=build(d['meta']['path'],254);rules(E);before=len(E.cnf.clauses);U={v for v in range(512) if (v^2).bit_count()<=2};add_cut(E,g,m,U,E.centres[0]);assert E.cnf.clauses[before:]==t['added_static_clauses']
 n=len(d['clauses']);delta=len(t['added_static_clauses']);cs=d['clauses']+t['added_static_clauses'];prefix=[{'clause':p['clause'],'hints':[i if i<=n else i+delta for i in p['hints']]} for p in d['proof']]
 result=check(cs,prefix+t['proof_tail'],require_empty=False);print(json.dumps({'shape':shape,'static_cut_rebuilt':True,'full_RUP':result,'scope':'CNF and hand-proved cut conditions; not Lean'}))
