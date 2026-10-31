"""Add the project's proved alpha rules; keep all original binary checkpoints intact.
New geometric premises need their own Lean bridge; this script makes no Lean claim.
"""
from pathlib import Path
import sys,json,gzip,hashlib,argparse,time
H=Path(__file__).resolve().parent;B=H.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from github_query import build,bank_witness,REPO
from gt_cost_comparison import control
from solver import Solver
from rup_check import check
from geometry_check import verify_cycle
from research_loop import save

def rules(E):
 C=E.cnf;before=len(C.clauses);A={x:[(l,1) for l,w in E.by_centre[x] if w==21] for x in E.centres}
 assert all(len(t)==36 for t in A.values())
 le={x:[C.leq_binary(t,k) for k in range(4)] for x,t in A.items()}
 eq1={x:C.AND(le[x][1],-le[x][0]) for x in E.centres};eq2={x:C.AND(le[x][2],-le[x][1]) for x in E.centres}
 for x in E.centres:C.clauses.append([-le[x][0]])
 for x,y in zip(E.centres,E.centres[1:]):C.clauses.extend([[-eq1[x],-le[y][3]],[-eq1[y],-le[x][3]]])
 for x,y,z in zip(E.centres,E.centres[1:],E.centres[2:]):C.clauses.append([-eq2[x],-eq2[y],-eq2[z]])
 return C.clauses[before:]

def run(shape,seconds):
 start=time.perf_counter();path=[0]
 for d in map(int,shape):path.append(path[-1]^(1<<d))
 E,g,m,meta=build(path,254);base=[c[:] for c in E.cnf.clauses]
 old=H/f'loop_k3_cap254_r4_d{shape}_all8'
 with gzip.open(old/'static8.json.gz','rt') as f:manifest=json.load(f)
 cycles=[c for c in manifest['cycles'] if not set(c)&E.forbidden]
 for c in cycles:verify_cycle(c)
 base.extend([[-E.var[v] for v in c] for c in cycles]);n=len(base)
 with gzip.open(old/'checkpoint.json.gz','rt') as f:prior=json.load(f)
 assert not prior['cuts'];assert hashlib.sha256(json.dumps(base,separators=(',',':')).encode()).hexdigest()==prior['CNF_sha256']
 additions=rules(E);cs=base+additions;delta=len(additions)
 proof=[{'clause':p['clause'],'hints':[i if i<=n else i+delta for i in p['hints']]} for p in prior['prefix_proof']]
 out=H/f'alpha_rules_d{shape}';out.mkdir(exist_ok=True)
 phase=prior.get('heuristic_phase_true',list(E.var.values()))
 if (out/'experiment.json.gz').exists():
  with gzip.open(out/'experiment.json.gz','rt') as f:saved=json.load(f)
  if saved['clauses']!=cs:raise ValueError('cannot resume: changed static CNF')
  proof=saved['proof'];phase=saved.get('phase_true',phase)
  if proof and proof[-1]['clause']==[]:
   check(cs,proof);print('already checked UNSAT');return
 checked_prior=check(cs,proof,require_empty=False)
 bank=json.loads((REPO/'work/bank9.json').read_text());S,p=control(tuple(map(int,shape)),bank);assert p==path
 # The bank need not satisfy cap254; every other old/new clause must hold.
 assignment=bank_witness(E,g,m,S);target=len(E.cnf.clauses)-len(additions)-1
 assert all(any(assignment[abs(l)]==(l>0) for l in c) for i,c in enumerate(E.cnf.clauses) if i!=target)
 solver=Solver(cs+[p['clause'] for p in proof],E.cnf.nv,primary=E.var.values(),phase_true=phase)
 init=time.perf_counter();result=solver.solve(seconds=seconds);verification=check(cs+[p['clause'] for p in proof],solver.proof,require_empty=result['status']=='UNSAT')
 model=result.pop('model',None)
 if model:assert all(any((l in model) for l in c) for c in cs)
 out=H/f'alpha_rules_d{shape}';out.mkdir(exist_ok=True)
 save(out/'experiment.json.gz',{'meta':meta,'premises':'project singleton; alpha1 neighbor>=4; no triple222','clauses':cs,'proof':proof+solver.proof,'model':model,'phase_true':[v for v in range(1,solver.n+1) if solver.phase[v]>0]})
 report={'shape':shape,'status':result['status'],'solver':result,'new_rule_clauses':delta,'variables':E.cnf.nv,'static_clauses':len(cs),'prior_proof_checked':checked_prior,'new_proof_checked':verification,'full_proof_steps':len(proof)+len(solver.proof),'bank_canonical_control':True,'wall_preparation_seconds':init-start,'wall_total_seconds':time.perf_counter()-start,'Lean_checked':False,'new_upper_bound':None}
 (out/'result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--shape',choices=['0120','0123'],required=True);a.add_argument('--seconds',type=float,default=30);args=a.parse_args();run(args.shape,args.seconds)
