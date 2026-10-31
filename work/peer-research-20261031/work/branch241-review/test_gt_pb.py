"""Exhaustive input checks and propagation refutations for wrong GT thresholds."""
from pathlib import Path
from itertools import product
import sys,random,json
R=Path(__file__).resolve().parent;B=R.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from pb_binary import BinaryCNF
from gt_pb import GeneralizedTotalizer

def conflict(cs):
 a={}
 while True:
  changed=False
  for c in cs:
   unknown=[];sat=False
   for l in c:
    if abs(l) not in a:unknown.append(l)
    elif a[abs(l)]==(l>0):sat=True;break
   if sat:continue
   if not unknown:return True
   if len(unknown)==1:
    l=unknown[0];a[abs(l)]=l>0;changed=True
  if not changed:return False

def main():
 rng=random.Random(77868254);assignments=0;invalid=0
 cases=[([2,3,7],cap) for cap in range(-2,15)]
 for weights,cap in cases:
  C=BinaryCNF();xs=[C.fresh() for _ in weights];terms=list(zip(xs,weights));G=GeneralizedTotalizer(C,terms,cap)
  for bits in product((False,True),repeat=3):
   a=G.extend(C.witness(dict(zip(xs,bits))));assert C.satisfied(a)
   good=sum(w for w,b in zip(weights,bits) if b)<=cap
   assert (a[abs(G.target)]==(G.target>0))==good
   fixed=[[x if b else -x] for x,b in zip(xs,bits)];assert conflict(C.clauses+fixed+[[G.target]])== (not good)
   assignments+=1
 for _ in range(200):
  C=BinaryCNF();xs=[C.fresh() for _ in range(3)];pool=xs+[-x for x in xs]+[C.one,-C.one];terms=[(rng.choice(pool),rng.randrange(0,20)) for _ in range(9)];cap=rng.randrange(-2,110);G=GeneralizedTotalizer(C,terms,cap)
  for bits in product((False,True),repeat=3):
   inputs=dict(zip(xs,bits));a=G.extend(C.witness(inputs));assert C.satisfied(a)
   truth=lambda l:a[abs(l)]==(l>0)
   good=sum(w for l,w in terms if truth(l))<=cap
   assert truth(G.target)==good
   assert conflict(C.clauses+[[x if b else -x] for x,b in zip(xs,bits)]+[[G.target]])==(not good)
   assignments+=1
 # Deliberately demonstrate nonunique auxiliaries at the same all-false input.
 C=BinaryCNF();x,y=C.fresh(),C.fresh();G=GeneralizedTotalizer(C,[(x,1),(y,1)],1);extensions=0
 for bits in product((False,True),repeat=C.nv-3):
  a={C.one:True,x:False,y:False,**dict(zip(range(4,C.nv+1),bits))}
  if C.satisfied(a) and a[abs(G.target)]==(G.target>0):extensions+=1
 assert extensions==2
 for term,cap in [([(0,1)],1),([(2,-1)],1),([(2,1.5)],1),([(2,1)],1.2)]:
  C=BinaryCNF();C.fresh()
  try:GeneralizedTotalizer(C,term,cap)
  except ValueError:invalid+=1
 assert invalid==4
 result={'all_input_assignments_checked':assignments,'wrong_thresholds_refuted_by_unit_propagation':True,'canonical_extensions_checked':True,'nonunique_auxiliary_extensions_example':extensions,'bad_inputs_rejected':invalid,'status':'PASS; prototype, no Lean claim'}
 (R/'gt_pb_tests.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
