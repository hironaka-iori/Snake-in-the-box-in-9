"""Exhaust all gate auxiliary assignments, not just canonical witnesses."""
import itertools,json,sys
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]/'branch241-next'
sys.path[:0]=[str(BASE/'encoding'),str(BASE)]
from pb_binary import BinaryCNF

def test():
 rows=[];total=0
 specs={'AND':3,'XOR':2,'MAJ':3,'ITE':3}
 for op,arity in specs.items():
  cases=0
  # signed, repeated, complementary and constant input combinations
  for indexes in itertools.product(range(6),repeat=arity):
   C=BinaryCNF();x,y=C.fresh(),C.fresh();pool=[x,-x,y,-y,C.one,-C.one];ls=[pool[i] for i in indexes]
   out=getattr(C,op)(*ls)
   aux=list(range(4,C.nv+1))
   for xv,yv in itertools.product((False,True),repeat=2):
    base={C.one:True,x:xv,y:yv};vals=[base[abs(l)]==(l>0) for l in ls]
    expected=all(vals) if op=='AND' else vals[0]!=vals[1] if op=='XOR' else sum(vals)>=2 if op=='MAJ' else vals[1] if vals[0] else vals[2]
    extensions=0
    for bits in itertools.product((False,True),repeat=len(aux)):
     assignment={**base,**dict(zip(aux,bits))}
     if C.satisfied(assignment):
      extensions+=1;assert (assignment[abs(out)]==(out>0))==expected,(op,ls,assignment)
     cases+=1
    assert extensions==1,(op,ls,base,extensions)
  rows.append({'operation':op,'all_auxiliary_assignments_checked':cases});total+=cases
 result={'checks':rows,'total_assignments':total,'all_gates_have_unique_correct_extension':True}
 (Path(__file__).parent/'gate_reverse_results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':test()
