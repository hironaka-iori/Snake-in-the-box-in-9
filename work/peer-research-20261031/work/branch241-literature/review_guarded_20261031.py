from pathlib import Path
import sys,json,gzip,hashlib,time
H=Path(__file__).resolve().parent;R=H.parent/'branch241-review'
sys.path[:0]=[str(H),str(R)]
from cutset_cnf import build,add_cut
from alpha_rules_probe import rules
from geometry_check import verify_cycle
from rup_check import check

def read(p):
 with gzip.open(p,'rt') as f:return json.load(f)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for shape in ['0120','0123']:
 start=time.perf_counter();source=R/f'portfolio_results/merged_{shape}.json.gz';base=read(source);p=H/f'cut_probes/{shape}.json.gz';old=read(p)
 assert sha(source)==old['summary']['source_checkpoint_sha256']
 E,g,m,meta=build(base['meta']['path'],254);static=E.cnf.clauses[:]
 manifest=read(R/f'loop_k3_cap254_r4_d{shape}_all8/static8.json.gz')
 assert manifest['allowed']==sorted(E.var)
 kept=[]
 for c in manifest['cycles']:
  verify_cycle(c)
  if not set(c)&E.forbidden:kept.append([-E.var[v] for v in c])
 static+=kept;static+=rules(E)
 assert static==base['clauses']
 before=len(E.cnf.clauses);cut=add_cut(E,g,m,{v for v in range(512) if (v^2).bit_count()<=2},E.centres[0]);new=E.cnf.clauses[before:]
 assert new==old['added_static_clauses'];n=len(static);delta=len(new);static+=new
 prefix=[{'clause':x['clause'],'hints':[i if i<=n else i+delta for i in x['hints']]} for x in base['proof']]
 prefix_result=check(static,prefix,require_empty=False)
 tail_result=check(static+[x['clause'] for x in prefix],old['proof_tail'],require_empty=old['summary']['status']=='UNSAT')
 assert prefix_result==old['summary']['shifted_prefix_checked'];assert tail_result==old['summary']['tail_checked']
 assert not any(not x['clause'] for x in prefix+old['proof_tail'])
 row={'shape':shape,'source_sha256':sha(source),'probe_sha256':sha(p),'static_sha256':hashlib.sha256(json.dumps(static,separators=(',',':')).encode()).hexdigest(),'static_clauses':len(static),'prefix':prefix_result,'tail':tail_result,'verified_induced_cycle_entries':len(manifest['cycles']),'status':'UNKNOWN','wall_seconds':time.perf_counter()-start}
 rows.append(row);print(json.dumps(row),flush=True)
(H/'guarded_cut_review_2026-10-31.json').write_text(json.dumps({'date':'2026-10-31','independent_full_reconstruction_and_RUP':'PASS','results':rows},indent=2))
