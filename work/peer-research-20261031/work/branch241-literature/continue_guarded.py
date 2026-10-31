"""Durable checked continuation of the guarded-cut experiment. No old checkpoint edits."""
from pathlib import Path
import sys,gzip,json,hashlib,argparse,time,math,os
if not __debug__:raise RuntimeError('verification requires Python without -O')
H=Path(__file__).resolve().parent;R=H.parent/'branch241-review';sys.path[:0]=[str(R),str(H)]
from cutset_cnf import build,add_cut
from alpha_rules_probe import rules
from solver_reduced import Solver
from rup_check import check
from research_loop import save
from charge_fast import Charges,Geometry
from geometry_check import components,verify_cycle

def run(shape,seconds,strategy):
 O=H/'guarded_runs';O.mkdir(exist_ok=True);path=O/f'{shape}.json.gz'
 if path.exists():
  with gzip.open(path,'rt') as f:d=json.load(f)
 else:
  source=R/f'portfolio_results/merged_{shape}.json.gz'
  with gzip.open(source,'rt') as f:base=json.load(f)
  with gzip.open(H/f'cut_probes/{shape}.json.gz','rt') as f:old=json.load(f)
  assert hashlib.sha256(source.read_bytes()).hexdigest()==old['summary']['source_checkpoint_sha256']
  E,g,m,meta=build(base['meta']['path'],254);rules(E);before=len(E.cnf.clauses);cut=add_cut(E,g,m,{v for v in range(512) if (v^2).bit_count()<=2},E.centres[0]);new=E.cnf.clauses[before:];assert new==old['added_static_clauses']
  n=len(base['clauses']);delta=len(new);cs=base['clauses']+new
  prefix=[{'clause':p['clause'],'hints':[i if i<=n else i+delta for i in p['hints']]} for p in base['proof']]+old['proof_tail']
  d={'clauses':cs,'proof':prefix,'meta':meta,'cut':cut,'phase_true':base.get('phase_true',[]),'history':[],'nvars':E.cnf.nv,'vertex_vars':E.var,'status':'UNKNOWN','origin_sha256':old['summary']['source_checkpoint_sha256']}
 # Rebuild the mathematical static formula on EVERY resume, not only a checksum.
 E,g,m,_=build(d['meta']['path'],254);rebuilt=E.cnf.clauses[:]
 with gzip.open(R/f'loop_k3_cap254_r4_d{shape}_all8/static8.json.gz','rt') as f:manifest=json.load(f)
 assert manifest['allowed']==sorted(E.var)
 active_cycles=[c for c in manifest['cycles'] if not set(c)&E.forbidden]
 for c in active_cycles:verify_cycle(c)
 rebuilt += [[-E.var[v] for v in c] for c in active_cycles]
 rebuilt += rules(E);before=len(E.cnf.clauses);add_cut(E,g,m,{v for v in range(512) if (v^2).bit_count()<=2},E.centres[0]);rebuilt += E.cnf.clauses[before:]
 assert rebuilt==d['clauses'] and E.cnf.nv==d['nvars']
 assert E.var=={int(v):x for v,x in d['vertex_vars'].items()}
 d['verification_sources_sha256']={str(p.name):hashlib.sha256(p.read_bytes()).hexdigest() for p in [H/'cutset_cnf.py',R/'rup_check.py',R/'alpha_rules_probe.py',R/'solver_reduced.py']}
 d['static_sha256']=hashlib.sha256(json.dumps(rebuilt,separators=(',',':')).encode()).hexdigest()
 if d['status'] in ['SAT','UNSAT']:
  check(d['clauses'],d['proof'],require_empty=d['status']=='UNSAT')
  if d['status']=='SAT':
   model=d.get('local_model',{}).get('model')
   if model is None:raise ValueError('missing saved SAT witness')
   a=set(model)
   if len(model)!=d['nvars'] or any((v in a)==(-v in a) for v in range(1,d['nvars']+1)):raise ValueError('inconsistent SAT witness')
   if not all(any(l in a for l in c) for c in d['clauses']):raise ValueError('saved model does not satisfy static formula')
  print('already',d['status']);return
 start=time.perf_counter();round=len(d['history'])+1
 (O/f'{shape}_running.json').write_text(json.dumps({'stage':'PREFIX_CHECK_AND_CONSTRUCTOR','round':round,'budget':seconds}))
 S=Solver(d['clauses'],d['proof'],nvars=d['nvars'],primary=d['vertex_vars'].values(),phase_true=d['phase_true'],restart=strategy,seed=103+17*round)
 init=time.perf_counter()-start;(O/f'{shape}_running.json').write_text(json.dumps({'stage':'SEARCH','round':round,'budget':seconds,'init_seconds':init}))
 result=S.solve(seconds=seconds);model=result.pop('model',None);checked=check(d['clauses']+[p['clause'] for p in d['proof']],S.proof,require_empty=result['status']=='UNSAT')
 if model:
  a=set(model);assert all(any(l in a for l in c) for c in d['clauses']);selected=[int(v) for v,x in d['vertex_vars'].items() if x in a];Q=Charges(Geometry(9),selected);q=sum(Q.cheap()['r6plus']['values'][v] for v in d['meta']['path'][1:-1]);assert q<=254
  d['local_model']={'model':model,'selected':selected,'qsum':q,'components':components(selected),'warning':'local relaxation; global snake not established'}
 d['proof']+=S.proof;d['phase_true']=[v for v in range(1,S.n+1) if S.phase[v]>0];d['status']=result['status'];d['checked']={'RUP_steps_checked':len(d['proof']),'unit_hints_checked':S.prefix_check['unit_hints_checked']+checked['unit_hints_checked'],'empty_clause_checked':result['status']=='UNSAT'}
 row={'round':round,'shape':shape,'solver':result,'new_RUP':checked,'all_RUP':d['checked'],'init_and_prefixcheck_seconds':init,'wall_before_save':time.perf_counter()-start};d['history'].append(row);save(path,d)
 (O/f'{shape}_running.json').write_text(json.dumps({'stage':'CHECKPOINT_SAVED','status':d['status'],'round':round}));(O/f'{shape}_summary.json').write_text(json.dumps(row,indent=2));print(json.dumps(row),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--batch-pid',type=int);p.add_argument('--shape',choices=['0120','0123'],required=True);p.add_argument('--seconds',type=float,default=120);p.add_argument('--restart',choices=['luby','lbd','geometric'],default='luby');a=p.parse_args()
 if not math.isfinite(a.seconds) or a.seconds<=0:raise ValueError('finite positive budget required')
 lockdir=H/'guarded_runs';lockdir.mkdir(exist_ok=True);batchlock=lockdir/f'{a.shape}_batch.lock'
 if batchlock.exists() and json.loads(batchlock.read_text())['pid']!=a.batch_pid:raise RuntimeError('batch owns this checkpoint')
 slicelock=lockdir/f'{a.shape}_slice.lock'
 with slicelock.open('x',encoding='utf-8') as f:json.dump({'pid':os.getpid()},f)
 try:run(a.shape,a.seconds,a.restart)
 finally:slicelock.unlink()
