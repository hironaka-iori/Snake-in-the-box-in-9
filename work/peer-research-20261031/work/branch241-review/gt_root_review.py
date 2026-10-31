"""Root review independent of GT author's propagation and witness tests."""
import itertools,json,sys,time
from pathlib import Path
R=Path(__file__).resolve().parent;B=R.parent/'branch241-next'
sys.path[:0]=[str(B),str(B/'encoding')]
from pb_binary import BinaryCNF
from gt_pb import GeneralizedTotalizer
from solver import Solver
from rup_check import check

def main():
 start=time.perf_counter();cases=0;refutations=0
 for weights in itertools.product(range(4),repeat=3):
  for cap in range(-1,sum(weights)+2):
   C=BinaryCNF();xs=[C.fresh() for _ in weights]
   # Correlated inputs x, not y, x XOR y exercise projected semantics.
   z=C.XOR(xs[0],xs[1]);terms=list(zip([xs[0],-xs[1],z],weights))
   G=GeneralizedTotalizer(C,terms,cap)
   for bits in itertools.product((False,True),repeat=2):
    a=G.extend(C.witness(dict(zip(xs,[*bits,False]))));assert C.satisfied(a)
    good=sum(w*(a[abs(l)]==(l>0)) for l,w in terms)<=cap
    assert (a[abs(G.target)]==(G.target>0))==good
    # Independent CDCL+RUP confirms impossibility, not just author's UP.
    if not good:
     cs=C.clauses+[[xs[i] if b else -xs[i]] for i,b in enumerate(bits)]+[[G.target]]
     S=Solver(cs,C.nv);out=S.solve(seconds=1);assert out['status']=='UNSAT';check(cs,S.proof);refutations+=1
    cases+=1
 result={'correlated_complete_assignments':cases,'above_cap_CDCL_RUP_refutations':refutations,'seconds':time.perf_counter()-start,'status':'PASS; independent root GT review, no new snake bound'}
 (R/'gt_root_review.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
