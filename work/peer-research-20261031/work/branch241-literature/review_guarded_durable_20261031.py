from pathlib import Path
import sys,json,gzip,hashlib,time
H=Path(__file__).resolve().parent;R=H.parent/'branch241-review';sys.path[:0]=[str(H),str(R)]
from cutset_cnf import build,add_cut
from alpha_rules_probe import rules
from geometry_check import verify_cycle
from rup_check import check
rows=[]
for shape in ['0120','0123']:
 t=time.perf_counter();p=H/f'guarded_runs/{shape}.json.gz';raw=p.read_bytes();startsha=hashlib.sha256(raw).hexdigest();d=json.loads(gzip.decompress(raw))
 E,g,m,_=build(d['meta']['path'],254);cs=E.cnf.clauses[:]
 with gzip.open(R/f'loop_k3_cap254_r4_d{shape}_all8/static8.json.gz','rt') as f:manifest=json.load(f)
 assert manifest['allowed']==sorted(E.var)
 cycles=[c for c in manifest['cycles'] if not set(c)&E.forbidden]
 for c in cycles:verify_cycle(c)
 cs += [[-E.var[v] for v in c] for c in cycles];cs += rules(E);n=len(E.cnf.clauses);add_cut(E,g,m,{v for v in range(512) if (v^2).bit_count()<=2},E.centres[0]);cs+=E.cnf.clauses[n:]
 assert cs==d['clauses'];assert E.cnf.nv==d['nvars'];assert E.var=={int(v):x for v,x in d['vertex_vars'].items()}
 digest=hashlib.sha256(json.dumps(cs,separators=(',',':')).encode()).hexdigest();assert 'static_sha256' not in d or digest==d['static_sha256']
 receipt=check(cs,d['proof'],require_empty=d['status']=='UNSAT');assert receipt==d['checked'];assert d['status']=='UNKNOWN';assert not any(not x['clause'] for x in d['proof'])
 endsha=hashlib.sha256(p.read_bytes()).hexdigest()
 row={'shape':shape,'snapshot_sha256':startsha,'path_sha256_after_check':endsha,'unchanged_during_review':startsha==endsha,'rounds_in_snapshot':len(d['history']),'stored_static_sha256_present':'static_sha256' in d,'status':d['status'],'static_clauses':len(cs),'static_sha256':digest,'full_RUP':receipt,'wall_seconds':time.perf_counter()-t}
 rows.append(row);print(json.dumps(row),flush=True)
(H/'guarded_durable_review_2026-10-31.json').write_text(json.dumps({'date':'2026-10-31','scope':'only the byte snapshots identified below; not future or concurrently replaced versions','reviewed_continue_guarded_sha256':hashlib.sha256((H/'continue_guarded.py').read_bytes()).hexdigest(),'results':rows},indent=2))
