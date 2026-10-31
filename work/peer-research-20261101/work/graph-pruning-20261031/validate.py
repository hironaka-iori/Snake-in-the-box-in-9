"""Independent brute-force and graph-structure checks; never substitute for Lean."""
from graph_solver import *
import random
HERE=Path(__file__).resolve().parent

def oracle(adj,R,h):
 def walk(path,seen):
  best=len(path)
  for v in bits(adj[path[-1]]&R&~seen):
   if adj[v]&(seen&~(1<<path[-1])):continue
   best=max(best,walk(path+[v],seen|(1<<v)))
  return best
 return walk([h],1<<h)

def check_graph(n,R,h):
 adj=cube(n);R=component(adj,R,h);exact=oracle(adj,R,h)
 values={'reach':R.bit_count(),'parity':parity_capacity(R,h),'leaf':leaf_bound(adj,R,h),'block':block_bound(adj,R,h),'claw':claw_bound(adj,R,h)}
 for K in combinations(list(bits(R)),2):
  assert separator_bound(adj,R,h,K)>=exact,(n,R,h,K,exact)
 assert all(b>=exact for b in values.values()),(n,list(bits(R)),h,values,exact)
 assert values['block']<=values['parity']
 return exact,values

def main():
 t=time.monotonic();cases=0;strict_block=0;strict_leaf=0
 for R in range(1,256):
  for h in bits(R):
   ex,v=check_graph(3,R,h);cases+=1;strict_block+=v['block']<v['parity'];strict_leaf+=v['block']<v['leaf']
 rng=random.Random(20261031)
 for _ in range(300):
  R=rng.randrange(1,1<<16);h=rng.choice(list(bits(R)));ex,v=check_graph(4,R,h);cases+=1;strict_block+=v['block']<v['parity'];strict_leaf+=v['block']<v['leaf']
 # Review counterexample: off-chain articulation vertices must remain in full blocks.
 R=sum(1<<v for v in [0,1,3,7,6,4,11,14]);exact,vals=check_graph(4,R,0)
 witness=[0,1,3,7,6,14];validate_path(cube(4),witness);assert exact==6 and vals['block']==6
 controls=[]
 for n,target,expected in [(2,2,'SAT'),(2,3,'UNSAT_EXHAUSTIVE_PYTHON'),(3,4,'SAT'),(3,5,'UNSAT_EXHAUSTIVE_PYTHON'),(4,7,'SAT'),(4,8,'UNSAT_EXHAUSTIVE_PYTHON')]:
  for mode in ['reach','parity','leaf','block','separator','claw','hybrid']:
   r=Search(n,target,mode=mode,node_limit=1000000,seconds=30).run();assert r['status']==expected,(n,target,mode,r);controls.append(r)
 r={'status':'PASS','graph_root_cases':cases,'strict_vs_parity':strict_block,'strict_vs_leaf':strict_leaf,'search_controls':controls,'off_chain_articulation_counterexample':{'vertices':list(bits(R)),'root':0,'witness':witness,'exact_vertices':exact,'bounds':vals},'seconds':time.monotonic()-t,'Lean_checked':False}
 (HERE/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='search_controls'},indent=2))
if __name__=='__main__':main()
