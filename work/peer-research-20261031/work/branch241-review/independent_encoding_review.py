"""Independent adversarial regression checks; no bank fixtures."""
from pathlib import Path
import sys,itertools,random,json,time
from fractions import Fraction
BASE=Path(__file__).resolve().parents[1]/'branch241-next'
sys.path[:0]=[str(BASE),str(BASE/'encoding')]
from charge_fast import Geometry,Charges
from cheap_folded import FixedPathObjective
from pb_binary import BinaryCNF

def direct(G,S,x):
 alpha=e2=e3=bonus=0
 for ds in itertools.combinations(range(G.n),2):
  face={x,x^(1<<ds[0]),x^(1<<ds[1]),x^(1<<ds[0])^(1<<ds[1])}
  alpha+=not(face-{x})&S
 a=Fraction(alpha)
 for axis in range(G.n):
  for ds in itertools.combinations([d for d in range(G.n) if d!=axis],2):
   f={x^(1<<axis)}
   for d in ds:f|={v^(1<<d) for v in list(f)}
   if f&S:continue
   e2+=1
   counts=[len({v^(1<<d) for v in f}&S) for d in range(G.n) if d not in ds]
   a+=Fraction(2,sum(t>0 for t in counts)*len({v^(1<<axis) for v in f}&S))
  for ds in itertools.combinations([d for d in range(G.n) if d!=axis],3):
   cube={x^(1<<axis)}
   for d in ds:cube|={v^(1<<d) for v in list(cube)}
   e3+=not cube&S
 for ds in itertools.combinations(range(G.n),3):
  cube={x}
  for d in ds:cube|={v^(1<<d) for v in list(cube)}
  chosen=cube&S
  if len(chosen)==1:bonus+=12
  elif len(chosen)==2:
   u,v=chosen;dist=(u^v).bit_count();bonus+=2 if dist==1 else 1 if dist==2 else 0
 return alpha,e2,e3,bonus,a

def run():
 start=time.perf_counter();small=roots=0;G=Geometry(3)
 for mask in range(256):
  S={v for v in range(8) if mask>>v&1}
  if any(set(vs)<=S for _,_,_,vs in G.squares):continue
  C=Charges(G,S);C.summary();small+=1
  for x in S:
   al,e2,e3,bo,a=direct(G,S,x)
   assert Fraction(C.a[x],G.A)==a and C.alpha[x]==al and C.e2[x]==e2
   roots+=1
 G=Geometry(9);rng=random.Random(839203);path=[0,1,3];E=FixedPathObjective(G,path,True,cnf_factory=BinaryCNF);tested=0
 for _ in range(80):
  S=set(path)|{v for v in E.ball if v not in E.forbidden and rng.random()<.13}
  if any(set(vs)<=S for _,_,_,vs in G.squares):continue
  C=Charges(G,S);cheap=C.cheap()['r6plus']['values'];got=E.evaluate(S)
  for x in E.centres:
   al,e2,e3,bo,a=direct(G,S,x)
   assert got[x]==cheap[x]==21*al+2*e2+e3+bo
   assert Fraction(got[x],21)<=a==Fraction(C.a[x],G.A)
  y=rng.choice(sorted(S-set(path)));C.remove(y);S.remove(y);D=Charges(G,S)
  assert (C.a,C.g,C.alpha,C.e2,C.summary())==(D.a,D.g,D.alpha,D.e2,D.summary());tested+=1
 pbcases=0
 for _ in range(120):
  spec=[(rng.randrange(3),rng.choice((-1,1)),rng.randrange(60)) for _ in range(9)];cap=rng.randrange(-2,350)
  C=BinaryCNF();xs=[C.fresh() for _ in range(3)];z=C.leq_binary([(xs[j]*s,w) for j,s,w in spec],cap)
  for bits in itertools.product((False,True),repeat=3):
   a=C.witness(dict(zip(xs,bits)));assert C.satisfied(a)
   expected=sum(w for j,s,w in spec if bits[j]==(s>0))<=cap
   assert (a[abs(z)]==(z>0))==expected;pbcases+=1
 result={'Q3_all_no_square_sets':small,'independent_selected_root_oracles':roots,'Q9_arbitrary_sets_and_deletions':tested,'random_signed_PB_assignments':pbcases,'seconds':time.perf_counter()-start,'status':'PASS; finite regression checks only'}
 (Path(__file__).parent/'independent_encoding_results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':run()
