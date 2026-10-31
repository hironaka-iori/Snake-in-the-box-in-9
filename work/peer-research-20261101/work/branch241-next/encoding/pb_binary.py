"""Exact positive-weight PB via carry-save binary addition and comparison.
Extension of the prototype equivalence CNF; no SAT/LRAT/Lean claim.
"""
from adaptive_pb import CNF
from collections import Counter
class BinaryCNF(CNF):
 def __init__(self):super().__init__();self.cache={}
 def AND(self,*ls):
  ls=set(ls)
  if -self.one in ls or any(-l in ls for l in ls):return -self.one
  ls.discard(self.one)
  if not ls:return self.one
  if len(ls)==1:return next(iter(ls))
  key=('and',tuple(sorted(ls)))
  if key not in self.cache:self.cache[key]=super().AND(*key[1])
  return self.cache[key]
 def XOR(self,a,b):
  if a==b:return -self.one
  if a==-b:return self.one
  if a==self.one:return -b
  if b==self.one:return -a
  if a==-self.one:return b
  if b==-self.one:return a
  key=('xor',tuple(sorted((a,b))))
  if key not in self.cache:
   z=self.fresh();self.clauses += [[-a,-b,-z],[a,b,-z],[a,-b,z],[-a,b,z]]
   self.gates.append((z,'xor',(a,b)));self.cache[key]=z
  return self.cache[key]
 def MAJ(self,a,b,c):
  if a==b or a==c:return a
  if b==c:return b
  if a==-b:return c
  if a==-c:return b
  if b==-c:return a
  if self.one in (a,b,c):return self.OR(*(x for x in (a,b,c) if x!=self.one))
  if -self.one in (a,b,c):return self.AND(*(x for x in (a,b,c) if x!=-self.one))
  key=('maj',tuple(sorted((a,b,c))))
  if key not in self.cache:
   z=self.fresh();self.clauses += [[-a,-b,z],[-a,-c,z],[-b,-c,z],[a,b,-z],[a,c,-z],[b,c,-z]]
   self.gates.append((z,'maj',(a,b,c)));self.cache[key]=z
  return self.cache[key]
 def witness(self,inputs):
  a={self.one:True,**inputs}
  def val(l):return a[abs(l)]==(l>0)
  for z,op,ls in self.gates:
   vs=list(map(val,ls));a[z]=all(vs) if op=='and' else (sum(vs)%2==1 if op=='xor' else sum(vs)>=2)
  return a
 def leq_binary(self,terms,cap):
  weights=Counter()
  for lit,w in terms:
   if w<0:raise ValueError('weights must be nonnegative')
   if w:weights[lit]+=w
  offset=weights.pop(self.one,0);weights.pop(-self.one,None)
  for lit in list(weights):
   if lit>0 and -lit in weights:
    k=min(weights[lit],weights[-lit]);offset+=k;weights[lit]-=k;weights[-lit]-=k
  terms=[(l,w) for l,w in weights.items() if w];cap-=offset;maximum=sum(w for _,w in terms)
  if cap<0:return -self.one
  if cap>=maximum:return self.one
  columns=[[] for _ in range(maximum.bit_length()+2)]
  for lit,w in terms:
   for bit in range(w.bit_length()):
    if w>>bit&1:columns[bit].append(lit)
  bits=[];carry=-self.one
  for i,col in enumerate(columns):
   while len(col)>2:
    a,b,c=col.pop(),col.pop(),col.pop();s=self.XOR(self.XOR(a,b),c);t=self.MAJ(a,b,c)
    if s!=-self.one:col.append(s)
    if t!=-self.one:columns[i+1].append(t)
   a=col[0] if col else -self.one;b=col[1] if len(col)>1 else -self.one
   bits.append(self.XOR(self.XOR(a,b),carry));carry=self.MAJ(a,b,carry)
  assert carry==-self.one
  # Processing low to high: high bit overrides lower comparison at first difference.
  ok=self.one
  for i,bit in enumerate(bits):
   ok=self.OR(-bit,ok) if cap>>i&1 else self.AND(-bit,ok)
  return ok

def self_test():
 import itertools,json
 cases=0
 for weights in ([2,3,5,7],[0,1,1,3],[1,2,4,8]):
  for cap in range(-1,sum(weights)+2):
   C=BinaryCNF();xs=[C.fresh() for _ in weights];terms=list(zip(xs,weights));target=C.leq_binary(terms,cap)
   for vals in itertools.product((False,True),repeat=len(xs)):
    a=C.witness(dict(zip(xs,vals)));assert C.satisfied(a)
    assert (a[abs(target)]==(target>0))==(sum(w for w,v in zip(weights,vals) if v)<=cap)
    cases+=1
 # signed literals, same/complement repeats, and constant offsets
 for cap in range(-1,20):
  C=BinaryCNF();x,y=C.fresh(),C.fresh();ts=[(x,3),(-x,2),(x,1),(y,7),(C.one,2),(-C.one,19)];t=C.leq_binary(ts,cap)
  for xv,yv in itertools.product((False,True),repeat=2):
   a=C.witness({x:xv,y:yv});assert C.satisfied(a);assert (a[abs(t)]==(t>0))==(4*xv+2*(not xv)+7*yv+2<=cap);cases+=1
 return {'complete_assignments_checked':cases,'exact_agreement':True}
if __name__=='__main__':
 import json;print(json.dumps(self_test(),indent=2))
