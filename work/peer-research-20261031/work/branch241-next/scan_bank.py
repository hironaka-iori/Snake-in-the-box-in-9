"""Resumable empirical scan of bank snakes/prefixes, never a universal proof."""
import json,time,sys,hashlib
from pathlib import Path
from charge_fast import Geometry,Charges
HERE=Path(__file__).resolve().parent; REPO=HERE.parent/'branch241-audit/repo'; OUT=HERE/'bank_scan.json'
G=Geometry(9); bank=json.loads((REPO/'work/bank9.json').read_text())
checkpoint={'bank_sha256':hashlib.sha256((REPO/'work/bank9.json').read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256((HERE/'charge_fast.py').read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'minimum_vertices':180}
report=json.loads(OUT.read_text()) if OUT.exists() and '--fresh' not in sys.argv else {'status':'EMPIRICAL SAMPLE ONLY, not universal window bounds','scale':G.A,'records':[],'complete':False}
if report['records'] and report.get('checkpoint')!=checkpoint:raise ValueError('checkpoint inputs/code changed; rerun with --fresh')
report['checkpoint']=checkpoint
done={r['bank_index'] for r in report['records']};start=time.perf_counter()
def canon(ds):
 m={};return [m.setdefault(d,len(m)) for d in ds]
for i,row in enumerate(bank):
 if i in done:continue
 path=row['vertex_sequence'];assert len(path)==len(set(path))
 for a in range(len(path)):
  for b in range(a+1,len(path)):assert ((path[a]^path[b]).bit_count()==1)==(b==a+1)
 c=Charges(G,path);record={'bank_index':i,'full':c.summary(),'prefix_sets_scanned':0,'undominated_prefixes':[],'minimum_windows':{}}
 for size in range(len(path),179,-1):
  if size<len(path):c.remove(path[size])
  p=path[:size];record['prefix_sets_scanned']+=1
  if c.U:record['undominated_prefixes'].append({'edges':size-1,'U':c.U})
  for k in (1,3,5,7,9):
   w=c.windows(p,k)
   if w is None:continue
   best=record['minimum_windows'].get(str(k))
   if best is None or w['sum_scaled']<best['sum_scaled']:
    first=w['first_vertex_index'];vs=p[first:first+k]
    ds=[(a^b).bit_length()-1 for a,b in zip(vs,vs[1:])]
    record['minimum_windows'][str(k)]={**w,'prefix_edges':size-1,'directions':canon(ds),'vertices':vs,'centre_scores_scaled':[c.a[x] for x in vs]}
 report['records'].append(record)
 report['complete']=len(report['records'])==len(bank)
 report['bank_count']=len(bank);report['sets_scanned']=sum(r['prefix_sets_scanned'] for r in report['records'])
 tmp=OUT.with_suffix('.tmp');tmp.write_text(json.dumps(report,indent=2));tmp.replace(OUT)
summary={'bank_count':len(bank),'sets_scanned':report['sets_scanned'],'complete':report['complete'],'runtime_this_run_seconds':time.perf_counter()-start,'entries_with_undominated_prefixes':[r['bank_index'] for r in report['records'] if r['undominated_prefixes']],'observed_minimum_windows':{}}
for k in (1,3,5,7,9):
 r=min(report['records'],key=lambda r:r['minimum_windows'][str(k)]['sum_scaled']);w=r['minimum_windows'][str(k)]
 summary['observed_minimum_windows'][str(k)]={'bank_index':r['bank_index'],**w,'mean_float_for_display':w['sum_scaled']/(G.A*k)}
(HERE/'bank_summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))
