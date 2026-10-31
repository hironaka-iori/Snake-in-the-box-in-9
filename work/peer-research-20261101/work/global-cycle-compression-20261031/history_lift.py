"""Sound finite-history lift for the audited model's geometrically impossible walk.
No global numerical improvement is claimed without rerunning the complete model.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
H=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('verification requires Python without -O')

@dataclass(frozen=True)
class Edge:
 id:int;u:int;v:int;weight:int

def lift_graph(edges,cycle_ids,max_run=6):
 """Only cycle vertices split; at most max_run*|cycle vertices| extra states."""
 ids=set(cycle_ids);byid={e.id:e for e in edges};assert len(byid)==len(edges) and ids<=byid.keys()
 special={v for i in ids for v in [byid[i].u,byid[i].v]};nodes=sorted({v for e in edges for v in [e.u,e.v]})
 states=[(v,r) for v in nodes for r in (range(max_run+1) if v in special else [0])];index={s:i for i,s in enumerate(states)};out=[];projection=[]
 for e in edges:
  for r in (range(max_run+1) if e.u in special else [0]):
   newr=r+1 if e.id in ids else 0
   if newr>max_run:continue
   out.append(Edge(len(out),index[e.u,r],index[e.v,newr],e.weight));projection.append(e.id)
 return states,out,projection

def accepts(ids,cycle_ids,max_run=6):
 run=0
 for e in ids:
  run=run+1 if e in cycle_ids else 0
  if run>max_run:return False
 return True

def min_mean_cycle(edges):
 adj={v:[] for e in edges for v in [e.u,e.v]}
 for e in edges:adj[e.u].append(e)
 best=None;attaining=None
 for start in sorted(adj):
  def visit(v,seen,weight,path):
   nonlocal best,attaining
   for e in adj[v]:
    if e.v==start:
     mean=Fraction(weight+e.weight,len(path)+1)
     if best is None or mean<best:best=mean;attaining=path+[e.id]
    elif e.v>start and e.v not in seen:visit(e.v,seen|{e.v},weight+e.weight,path+[e.id])
  visit(start,{start},0,[])
 return best,attaining

def validate():
 src=json.loads((H/'upstream_proved_analysis.json').read_text());C=[Edge(x['edge'],x['u'],x['v'],x['weight']) for x in src['cycle']];ids={e.id for e in C}
 assert all(C[i].v==C[(i+1)%4].u for i in range(4))
 states,lifted,projection=lift_graph(C,ids);assert len(states)==28 and len(lifted)==24
 assert min_mean_cycle(lifted)[0] is None
 # Compare ALL walks in a small graph against a direct forbidden-history scan.
 toy=[Edge(i,i,(i+1)%4,w) for i,w in enumerate([480,360,600,480])]+[Edge(4,0,4,1200),Edge(5,4,0,1200)]
 ss,ee,pr=lift_graph(toy,{0,1,2,3});out={s:[] for s in range(len(ss))};raw={v:[] for e in toy for v in [e.u,e.v]}
 for e in ee:out[e.u].append(e)
 for e in toy:raw[e.u].append(e)
 walks=0
 def go(v,lifted_state,history,depth):
  nonlocal walks
  assert accepts(history,{0,1,2,3})==(lifted_state is not None);walks+=1
  if not depth:return
  for e in raw[v]:
   cand=[] if lifted_state is None else [z for z in out[lifted_state] if pr[z.id]==e.id]
   assert len(cand)<=1
   go(e.v,cand[0].v if cand else None,history+[e.id],depth-1)
 for v in raw:go(v,ss.index((v,0)),[],15)
 before,_=min_mean_cycle(toy);after,_=min_mean_cycle(ee);assert before==480 and after==720
 # An untouched alternative cycle keeps the global mean at 480 in a counterexample model.
 plus=toy+[Edge(6,8,9,480),Edge(7,9,8,480)];_,pe,_=lift_graph(plus,{0,1,2,3});unaffected,_=min_mean_cycle(pe);assert unaffected==480
 mu=Fraction(480);R=578;bound=Fraction(1098960+8*mu+R,mu+4200);assert bound==Fraction(551689,2340)
 threshold=Fraction(1098960+R-235*4200,235-8);assert threshold==Fraction(112538,227)
 assert Fraction(1098960+8*496+578,496+4200)<235
 report={'status':'PASS','source_model_status':src['status'],'source_mean':src['integer_mean'],'source_range':src['potential_range'],'impossible_cycle_ids':[e.id for e in C],'max_consecutive_cycle_edges':6,'extra_states_in_full_graph':24,'cycle_only_lifted_states':len(states),'cycle_only_lifted_edges':len(lifted),'cycle_only_lift_acyclic':True,'toy_walks_checked':walks,'toy_mean_before':str(before),'toy_mean_after':str(after),'untouched_cycle_counterexample_mean':str(unaffected),'target235_required_mu_at_R578':str(threshold),'mu496_R578_bound':str(Fraction(1098960+8*496+578,496+4200)),'R_limit_at_mu496':631,'full_4957613_edge_model_recomputed':False,'new_global_bound':None,'Lean_checked':False}
 (H/'lift_validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':validate()
