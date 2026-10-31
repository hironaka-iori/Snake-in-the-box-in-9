from pathlib import Path
import sys,json
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H.parent/'branch241-review'));from all8_cycles import templates
perfect=[]
for C in templates():
 order=[C[0]]
 while len(order)<8:
  v=order[-1];order.append(next(w for w in C if (v^w).bit_count()==1 and w not in order))
 if all((order[i]^order[(i+4)%8]).bit_count()==4 for i in range(8)):perfect.append(order)
assert len(perfect)==24
r={'all_induced_Q4_C8_vertex_sets':len(templates()),'perfect_Q4_C8_vertex_sets':len(perfect),'not_perfect':len(templates())-len(perfect),'scope':'configuration density is not selected-set density'}
H.joinpath('perfect_cycle_scope.json').write_text(json.dumps(r,indent=2));print(r)
