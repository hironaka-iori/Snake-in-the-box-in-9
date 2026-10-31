"""Project-CNF adapter for guarded endpoint cutsets. Experimental, not Lean checked."""
from pathlib import Path
import sys,json
H=Path(__file__).resolve().parent;B=H.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding'),str(H.parent/'branch241-review')]
from github_query import build,bank_witness,REPO
from gt_cost_comparison import control
from global_cutsets import closed

def add_cut(E,geo,remap,U,root):
 U=set(U);n=9
 if root not in U or not closed(U,n)<=set(E.var):raise ValueError('incomplete cut boundary or absent root')
 endpoints={}
 inverse={i:v for v,i in geo.var.items()}
 for clause,kind in zip(geo.clauses,geo.kinds):
  if kind=='end_selected':endpoints[inverse[clause[1]]]=remap[-clause[0]]
 if not U<=endpoints.keys():raise ValueError('global endpoint witness missing for cut vertex')
 C=E.cnf;before=len(C.clauses);cross=[]
 for u in sorted(U):
  for d in range(n):
   v=u^(1<<d)
   if v not in U:cross.append(C.AND(E.var[u],E.var[v]))
 # cross+ends >= 2*selected(root); exact positive PB after complementing terms.
 terms=[(-x,1) for x in cross]+[(-endpoints[u],1) for u in sorted(U)]+[(E.var[root],2)]
 C.clauses.append([C.leq_binary(terms,len(cross)+len(U))])
 return {'root':root,'U_vertices':len(U),'cross_edges':len(cross),'new_clauses':len(C.clauses)-before,'boundary_guard':True}

def main():
 bank=json.loads((REPO/'work/bank9.json').read_text());rows=[]
 for shape in ['0120','0123']:
  S,path=control(tuple(map(int,shape)),bank);E,g,m,meta=build(path,254);old_target=len(E.cnf.clauses)-1;nv=E.cnf.nv
  U={v for v in range(512) if (v^2).bit_count()<=2};r=add_cut(E,g,m,U,path[1]);a=bank_witness(E,g,m,S)
  assert all(any(a[abs(l)]==(l>0) for l in c) for i,c in enumerate(E.cnf.clauses) if i!=old_target)
  r.update(shape=shape,new_variables=E.cnf.nv-nv,actual_bank_all_added_clauses_satisfied=True);rows.append(r)
 result={'scope':'guarded necessary-condition CNF prototype; no threshold UNSAT or Lean claim','cuts':rows};H.joinpath('cutset_cnf_controls.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
