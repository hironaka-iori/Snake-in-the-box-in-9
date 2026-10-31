"""Standalone bounded GT experiments; leaves binary builders/checkpoints unchanged.
Default: both canonical three-centre shapes, cap254, at most 10 solve seconds each.
"""
from pathlib import Path
import argparse,gzip,json,sys,time,hashlib,gc
R=Path(__file__).resolve().parent;B=R.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from github_query import build,bank_witness,REPO
from pb_binary import BinaryCNF
from charge_fast import Geometry,Charges
from gt_pb import GeneralizedTotalizer
from gt_cost_comparison import control
from solver import Solver
from rup_check import check
from geometry_check import verify_cycle,components
from independent_global_snake import validate


def build_gt(path,cap):
 original=BinaryCNF.leq_binary
 def override(self,terms,residual_cap):
  self._gt_pb=GeneralizedTotalizer(self,terms,residual_cap);return self._gt_pb.target
 try:
  BinaryCNF.leq_binary=override
  E,g,m,meta=build(path,cap)
 finally:BinaryCNF.leq_binary=original
 E.gt_pb=E.cnf._gt_pb;meta['PB_encoding']='forward generalized totalizer; existential auxiliaries'
 return E,g,m,meta


def run(shape,path,cap,seconds,out):
 start=time.perf_counter();out.mkdir(parents=True,exist_ok=True);E,g,m,meta=build_gt(path,cap);target_index=len(E.cnf.clauses)-1;GT=E.gt_pb
 bank=json.loads((REPO/'work/bank9.json').read_text());S,window=control(tuple(map(int,shape)),bank);assert window==path;validate(S,path)
 a=GT.extend(bank_witness(E,g,m,S));assert len(a)==E.cnf.nv
 assert all(any(a[abs(l)]==(l>0) for l in c) for c in E.cnf.clauses[:target_index])
 exact=Charges(Geometry(9),S).cheap()['r6plus'];bank_score=sum(exact['values'][x] for x in E.centres)
 assert (a[abs(GT.target)]==(GT.target>0))==(bank_score<=cap)
 bank_control={'known_genuine_snake':True,'complete_canonical_extension':True,'all_pre_target_clauses_satisfied':True,'score':bank_score,'target_truth_exact':True,'query_cap_satisfied':bank_score<=cap};del a,bank,S;gc.collect()
 manifest_path=R/f'loop_k3_cap254_r4_d{shape}_all8/static8.json.gz'
 with gzip.open(manifest_path,'rt',encoding='utf-8') as f:manifest=json.load(f)
 assert manifest['allowed']==sorted(E.var)
 active=[c for c in manifest['cycles'] if not set(c)&E.forbidden]
 units={c[0] for c in E.cnf.clauses if len(c)==1};assert all(-E.var[v] in units for v in E.forbidden)
 for c in active:verify_cycle(c)
 E.cnf.clauses.extend([[-E.var[v] for v in c] for c in active]);clauses=E.cnf.clauses
 digest=hashlib.sha256(json.dumps(clauses,separators=(',',':')).encode()).hexdigest();build_done=time.perf_counter()
 solver=Solver(clauses,E.cnf.nv,primary=E.var.values(),phase_true=E.var.values());init_done=time.perf_counter();result=solver.solve(seconds=seconds);solve_done=time.perf_counter()
 proof_check=check(clauses,solver.proof,require_empty=result['status']=='UNSAT');check_done=time.perf_counter();model=result.pop('model',None);decoded=None
 if model is not None:
  a={abs(l):l>0 for l in model};assert all(any(a[abs(l)]==(l>0) for l in c) for c in clauses)
  selected=[v for v,var in E.var.items() if a[var]];score=Charges(Geometry(9),selected).cheap()['r6plus'];cost=sum(score['values'][x] for x in E.centres);assert cost<=cap
  comps=components(selected);cycles=[c for c in comps if all(sum(v^(1<<d) in set(c) for d in range(9))==2 for v in c)]
  decoded={'selected':selected,'score_scaled21':cost,'cycle_sizes':list(map(len,cycles)),'warning':'local necessary-condition model, not a certified global snake'}
 summary={'shape':shape,'cap_scaled21':cap,'solve_budget_seconds':seconds,'solver':result,'checked_new_proof':proof_check,'bank_canonical_control':bank_control,'GT':GT.statistics(),'variables':E.cnf.nv,'clauses':len(clauses),'static8_full':len(manifest['cycles']),'static8_folded':len(active),'CNF_sha256':digest,'wall_build_and_controls_seconds':build_done-start,'wall_solver_init_seconds':init_done-build_done,'wall_solve_seconds':solve_done-init_done,'wall_proof_check_seconds':check_done-solve_done,'Lean_checked':False}
 payload={'meta':meta,'summary':summary,'clauses':clauses,'proof':solver.proof,'model':model,'decoded':decoded}
 with gzip.open(out/'experiment.json.gz','wt',encoding='utf-8',compresslevel=1) as f:json.dump(payload,f,separators=(',',':'))
 summary['wall_seconds_including_build_init_check_save']=time.perf_counter()-start
 (out/'result.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary),flush=True);return summary


def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=10);ap.add_argument('--cap',type=int,default=254);ap.add_argument('--shapes',nargs='+',choices=['0120','0123'],default=['0120','0123']);ap.add_argument('--out',type=Path,default=R/'GT_probes');args=ap.parse_args()
 if not 0<args.seconds<=10:raise ValueError('standalone probe permits at most 10 solve seconds')
 rows=[]
 for shape in args.shapes:
  path=[0]
  for d in map(int,shape):path.append(path[-1]^(1<<d))
  rows.append(run(shape,path,args.cap,args.seconds,args.out/('d'+shape)));gc.collect()
 (args.out/'summary.json').write_text(json.dumps(rows,indent=2))
if __name__=='__main__':main()
