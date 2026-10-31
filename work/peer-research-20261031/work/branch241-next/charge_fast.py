"""Exact bitset empty-face charges and incremental prefix updates.
No solver or floating-point arithmetic. Scores require an induced set without 4-cycles.
The engine checks this condition. Scores do not constitute universal window lower bounds.
"""
from itertools import combinations
from math import lcm,gcd

class Geometry:
 def __init__(self,n=9):
  if not 3<=n<=9: raise ValueError('supported dimensions 3..9')
  self.n=n; self.N=1<<n;self.squares=[];self.cubes=[]
  for k,dst in ((2,self.squares),(3,self.cubes)):
   for ds in combinations(range(n),k):
    free=sum(1<<d for d in ds)
    for b in range(self.N):
     if b&free:continue
     vs=[b]
     for d in ds: vs += [x^(1<<d) for x in vs]
     dst.append((sum(1<<v for v in vs),tuple(ds),b,tuple(vs)))
  lookup={m:i for i,(m,*_) in enumerate(self.squares)}
  self.opposite=[];self.at=[[] for _ in range(self.N)]
  for i,(m,ds,b,vs) in enumerate(self.squares):
   self.opposite.append(tuple(lookup[sum(1<<(v^(1<<d)) for v in vs)] for d in range(n) if d not in ds))
   for v in vs:self.at[v].append(i)
  self.cube_boundary=[sum(1<<(v^(1<<d)) for d in range(n) if d not in ds for v in vs) for _,ds,_,vs in self.cubes]
  self.affected=[tuple(sorted(set(self.at[v]).union(*(self.opposite[f] for f in self.at[v])))) for v in range(self.N)]
  den=lcm(*(h*q for h in range(1,n-1) for q in (1,2,3)))
  self.A=den//gcd(den,2)
  self.G=lcm(*((n-2)*q//gcd(2,(n-2)*q) for q in (1,2,3)))
 def mask(self,vertices):
  vs=list(vertices)
  if len(vs)!=len(set(vs)) or any(not 0<=v<self.N for v in vs):raise ValueError('invalid vertex set')
  return sum(1<<v for v in vs)

class Charges:
 def __init__(self,geo,vertices):
  self.geo=geo;self.S=geo.mask(vertices);self.a=[0]*geo.N;self.g=[0]*geo.N
  self.alpha=[0]*geo.N;self.e2=[0]*geo.N;self._moments=None
  self.T=self.E2=self.U=0
  for i,(m,*_) in enumerate(geo.squares):
   if self.S&m==m: raise ValueError('selected 4-cycle not supported by q<=3 scales')
   self._apply(i,1)
 def _apply(self,i,sign):
  G=self.geo; inside=self.S&G.squares[i][0];q=inside.bit_count()
  if q==1:
   x=inside.bit_length()-1;self.a[x]+=sign*G.A;self.g[x]+=sign*G.G;self.T+=sign;self.alpha[x]+=sign
  elif q==0:
   self.E2+=sign
   live=[self.S&G.squares[j][0] for j in G.opposite[i]];live=[m for m in live if m]
   h=len(live)
   if not h:self.U+=sign;return
   for m in live:
    q=m.bit_count()
    assert 1<=q<=3
    da,rem=divmod(2*G.A,h*q);dg,remg=divmod(2*G.G,(G.n-2)*q)
    assert rem==remg==0
    while m:
     bit=m&-m;x=bit.bit_length()-1;m^=bit
     self.a[x]+=sign*da;self.g[x]+=sign*dg;self.e2[x]+=sign
 def remove(self,v):
  if not self.S>>v&1:raise ValueError('vertex not selected')
  affected=self.geo.affected[v]
  for i in affected:self._apply(i,-1)
  self.S^=1<<v;self._moments=None
  for i in affected:self._apply(i,1)
  assert self.a[v]==self.g[v]==0
 def summary(self):
  G=self.geo;E3=sum(not(self.S&m) for m,*_ in G.cubes)
  assert sum(self.a)+2*G.A*self.U==G.A*(self.T+2*self.E2)
  assert (G.n-2)*sum(self.g)+12*G.G*E3==G.G*(G.n-2)*(self.T+2*self.E2)
  assert all(a*G.G>=g*G.A for a,g in zip(self.a,self.g))
  return {'vertices':self.S.bit_count(),'T':self.T,'E2':self.E2,'E3':E3,'U':self.U,'adaptive_scale':G.A,'uniform_scale':G.G,'adaptive_sum_scaled':sum(self.a),'uniform_sum_scaled':sum(self.g)}
 def windows(self,path,k):
  # Only internal centres; endpoints deliberately excluded.
  if self.S!=self.geo.mask(path):raise ValueError('path does not match set')
  vals=[self.a[v] for v in path[1:-1]]
  if len(vals)<k:return None
  score=sum(vals[:k]);best=(score,1)
  for j in range(k,len(vals)):
   score+=vals[j]-vals[j-k]
   if score<best[0]:best=(score,j-k+2)
  return {'sum_scaled':best[0],'first_vertex_index':best[1],'centres':k,'scale':self.geo.A}

 def moments(self):
  if self._moments is not None:return self._moments
  e3=[0]*self.geo.N;bonus=[0]*self.geo.N
  for (m,*_),boundary in zip(self.geo.cubes,self.geo.cube_boundary):
   inside=self.S&m;occ=inside.bit_count()
   if occ:
    if occ==1:bonus[inside.bit_length()-1]+=12
    elif occ==2:
     lo=inside&-inside;u=lo.bit_length()-1;v=(inside^lo).bit_length()-1;d=(u^v).bit_count();b=2 if d==1 else 1 if d==2 else 0;bonus[u]+=b;bonus[v]+=b
    continue
   chosen=self.S&boundary
   while chosen:
    bit=chosen&-chosen;e3[bit.bit_length()-1]+=1;chosen^=bit
  self._bonus=bonus
  self._moments=(self.e2,e3)
  return self._moments
 def cheap(self):
  if self.geo.n!=9:raise ValueError('support-line coefficients here specialize to Q9')
  e2,e3=self.moments();rows={}
  for name,scale,b,c in [('r3',6,0,1),('r4',30,2,3),('r5',45,4,3),('r6',21,2,1)]:
   values=[scale*a+b*u+c*w for a,u,w in zip(self.alpha,e2,e3)]
   assert all(x*self.geo.A<=y*scale for x,y in zip(values,self.a))
   rows[name]={'scale':scale,'values':values}
  for name,base,b in [('r4plus','r4',1),('r5plus','r5',2),('r6plus','r6',1)]:
   scale=rows[base]['scale'];values=[x+b*y for x,y in zip(rows[base]['values'],self._bonus)]
   assert all(x*self.geo.A<=y*scale for x,y in zip(values,self.a))
   rows[name]={'scale':scale,'values':values}
  values=[max(row['values'][i]*(630//row['scale']) for row in rows.values()) for i in range(self.geo.N)]
  rows['envelope']={'scale':630,'values':values}
  assert all(x*self.geo.A<=y*630 for x,y in zip(values,self.a))
  return rows
