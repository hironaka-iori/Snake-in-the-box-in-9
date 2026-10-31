"""Bounded, resumable project window search with checked learned clauses/cycle cuts.
A positive-hint RUP certificate proves only this static CNF; Lean bridge remains separate.
"""
import argparse,gzip,hashlib,json,sys,time,heapq,math
from pathlib import Path
HERE=Path(__file__).resolve().parent;BASE=HERE.parent/'branch241-next';sys.path[:0]=[str(BASE),str(BASE/'encoding')]
from github_query import build,REPO
from charge_fast import Geometry,Charges
from solver import Solver
from rup_check import check
from geometry_check import components,verify_cycle,verify_global_snake

def save(path,data):
 tmp=path.with_suffix(path.suffix+'.tmp')
 payload=json.dumps(data,separators=(',',':')).encode('utf-8')
 with gzip.open(tmp,'wb',compresslevel=1) as f:f.write(payload)
 tmp.replace(path)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--centres',type=int,default=1);ap.add_argument('--cap',type=int,default=21);ap.add_argument('--radius',type=int,default=4);ap.add_argument('--seconds',type=float,default=35);ap.add_argument('--slice-seconds',type=float,default=5);ap.add_argument('--max-rounds',type=int,default=100);ap.add_argument('--out',type=Path);ap.add_argument('--precycle8',action='store_true');ap.add_argument('--all8',action='store_true');ap.add_argument('--dirs');ap.add_argument('--static8-fold',action='store_true');args=ap.parse_args()
 if args.dirs:
  ds=[int(c) for c in args.dirs]
  if any(d not in range(9) for d in ds) or len(ds)<2:raise ValueError('at least two directions in 0..8 required')
  args.centres=len(ds)-1
 out=args.out or HERE/(f'loop_k{args.centres}_cap{args.cap}_r{args.radius}'+('_d'+args.dirs if args.dirs else '')+('_all8' if args.all8 else '_pre8' if args.precycle8 else ''));out.mkdir(parents=True,exist_ok=True)
 bank=json.loads((REPO/'work/bank9.json').read_text());path=bank[67]['vertex_sequence'][:args.centres+2]
 if args.dirs:
  path=[0]
  for d in ds:path.append(path[-1]^(1<<d))
 E,geo,remap,meta=build(path,args.cap,radius=args.radius);original=[c[:] for c in E.cnf.clauses]
 if args.all8 and args.precycle8:raise ValueError('choose all8 or precycle8, not both')
 static_cycles=[]
 if args.all8:
  from all8_cycles import enumerate_all8
  manifest_path=out/'static8.json.gz'
  if manifest_path.exists():
   with gzip.open(manifest_path,'rt',encoding='utf-8') as f:manifest=json.load(f)
   if manifest['allowed']!=sorted(E.var):raise ValueError('static8 manifest vertex domain differs')
   static_cycles=manifest['cycles']
  else:
   static_cycles,enumeration=enumerate_all8(E.var);save(manifest_path,{'allowed':sorted(E.var),'cycles':static_cycles,'enumeration':enumeration})
  meta['static8_full_count']=len(static_cycles);meta['static8_folded_by_fixed_forbidden']=args.static8_fold
  if args.static8_fold:static_cycles=[c for c in static_cycles if not set(c)&E.forbidden]
  for c in static_cycles:verify_cycle(c)
  if len({tuple(c) for c in static_cycles})!=len(static_cycles):raise ValueError('duplicate static cycles')
  original += [[-E.var[v] for v in c] for c in static_cycles]
  meta['static8_count']=len(static_cycles);meta['static8_manifest_sha256']=hashlib.sha256(manifest_path.read_bytes()).hexdigest()
 digest=hashlib.sha256(json.dumps(original,separators=(',',':')).encode()).hexdigest();checkpoint=out/'checkpoint.json.gz'
 if checkpoint.exists():
  with gzip.open(checkpoint,'rt',encoding='utf-8') as f:state=json.load(f)
  if state['CNF_sha256']!=digest:raise ValueError('checkpoint CNF differs')
  if state.get('precycle8',False)!=args.precycle8:raise ValueError('checkpoint pre-cycle configuration differs')
 else:state={'CNF_sha256':digest,'meta':meta,'cuts':[],'prefix_proof':[],'history':[],'status':'ACTIVE'}
 if not checkpoint.exists() and args.precycle8:
  from cycle_dfs import enumerate_cycles
  cycles,enumeration=enumerate_cycles(path[:3],8,allowed=E.var)
  state['cuts']=[{'vertices':list(c),'kind':'exhaustive_rooted8','prefix':path[:3]} for c in cycles];state['precycle8_enumeration']=enumeration
 state['precycle8']=args.precycle8
 if state['status'] in ('UNSAT','GLOBAL_SAT','LOCAL_SAT'):print(json.dumps({'status':state['status'],'already_complete':True}));return
 # Every saved cut is revalidated independently before it can be reused.
 cutkeys={tuple(c) for c in static_cycles}
 for item in state['cuts']:
  verify_cycle(item['vertices']);key=tuple(item['vertices']);assert key not in cutkeys;cutkeys.add(key)
 original += [[-E.var[v] for v in cut['vertices']] for cut in state['cuts']]
 prefix_verified=check(original,state['prefix_proof'],require_empty=False)
 start=time.perf_counter();deadline=start+args.seconds
 for loop in range(args.max_rounds):
  remaining=deadline-time.perf_counter()
  if remaining<=.1:break
  prefix=state['prefix_proof'];cs=original+[x['clause'] for x in prefix]
  solver=Solver(cs,E.cnf.nv,primary=E.var.values(),phase_true=state.get('heuristic_phase_true',list(E.var.values())))
  if 'heuristic_activity' in state:
   activity=state['heuristic_activity'];increment=state['heuristic_increment']
   if len(activity)!=solver.n+1 or any(not math.isfinite(v) or v<0 for v in activity) or not math.isfinite(increment) or increment<=0:raise ValueError('invalid saved heuristic')
   solver.activity=activity[:];solver.increment=increment;solver.heap=[(-activity[v],v) for v in range(1,solver.n+1) if not solver.values[v]];heapq.heapify(solver.heap)
  result=solver.solve(seconds=min(args.slice_seconds,remaining))
  # Check against the static base, not the solver's mutable watched clauses.
  combined=prefix+solver.proof;checked=check(cs,solver.proof,require_empty=result['status']=='UNSAT');state['prefix_proof']=combined
  prefix_verified={'RUP_steps_checked':len(combined),'unit_hints_checked':prefix_verified['unit_hints_checked']+checked['unit_hints_checked']}
  state['heuristic_phase_true']=[v for v in range(1,solver.n+1) if solver.phase[v]>0];state['heuristic_activity']=solver.activity[:];state['heuristic_increment']=solver.increment
  model=result.pop('model',None);round_index=len(state['history']);entry={**result,'proof_checked_new_tail':checked,'verified_prefix':prefix_verified.copy(),'round':round_index,'static_clauses':len(original),'cuts_before':len(state['cuts'])}
  if result['status']=='SAT':
   assignment={abs(l):l>0 for l in model};assert all(any(assignment[abs(l)]==(l>0) for l in c) for c in original)
   S=[v for v,var in E.var.items() if assignment[var]];C=Charges(Geometry(9),S);score=sum(C.cheap()['r6plus']['values'][x] for x in E.centres);assert score<=args.cap
   cycles=[c for c in components(S) if len(c)>2 and all(sum(v^(1<<d) in set(c) for d in range(9))==2 for v in c)]
   model_path=out/f'model_{round_index}.json.gz';save(model_path,{'model':model,'selected':S,'score_scaled21':score,'cuts_before':len(state['cuts'])});entry.update(model_file=model_path.name,score_scaled21=score,selected_vertices=len(S),cycle_lengths=list(map(len,cycles)))
   if not cycles:
    state['status']='GLOBAL_SAT' if args.radius==9 else 'LOCAL_SAT';state['selected']=S
    if args.radius==9:state['global_snake']=verify_global_snake(S,path)
   else:
    for c in cycles:
     verify_cycle(c);key=tuple(c);assert key not in cutkeys;cutkeys.add(key)
     state['cuts'].append({'vertices':c,'kind':'lazy_model_cycle','model_file':model_path.name,'round':round_index});original.append([-E.var[v] for v in c])
    # New geometric axioms change the static clause ID prefix. Restart learning cleanly.
    state['prefix_proof']=[];prefix_verified={'RUP_steps_checked':0,'unit_hints_checked':0}
  elif result['status']=='UNSAT':state['status']='UNSAT';state['checked_static_scope']='original window CNF + all independently validated cycle cuts'
  state['history'].append(entry);save(checkpoint,state)
  summary={'status':state['status'],'rounds':len(state['history']),'cuts':len(state['cuts']),'static8_cuts':len(static_cycles),'last':entry,'elapsed_this_run':time.perf_counter()-start}
  (out/'progress.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary),flush=True)
  if state['status']!='ACTIVE':break
 save(checkpoint,state)
 if state['status']=='UNSAT':save(out/'checked_unsat.json.gz',{'clauses':original,'proof':state['prefix_proof'],'cuts':state['cuts'],'static_cycles':static_cycles,'meta':meta,'CNF_sha256':digest})
 if state['status']=='GLOBAL_SAT':(out/'global_snake.json').write_text(json.dumps(state['global_snake'],indent=2))
 print('FINAL',json.dumps({'status':state['status'],'rounds':len(state['history']),'cuts':len(state['cuts']),'retained_learning':len(state['prefix_proof'])}),flush=True)
if __name__=='__main__':main()
