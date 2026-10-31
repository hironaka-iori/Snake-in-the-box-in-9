"""Optional proof-producing CDCL strategies. Original Solver remains unchanged.
No clause deletion and no unchecked inprocessing. Every result uses the same RUP checker.
"""
from solver import Solver as Base
import time,heapq,random

def luby(i):
 k=1
 while (1<<k)-1<i:k+=1
 return 1<<(k-1) if i==(1<<k)-1 else luby(i-(1<<(k-1))+1)

class Solver(Base):
 def __init__(self,*args,binary=True,circular=False,minimize=False,restart='lbd',seed=0,**kwargs):
  if restart not in ('geometric','luby','lbd'):raise ValueError('unknown restart strategy')
  self.optimized=False;self.binary_enabled=binary;self.circular=circular;self.minimize=minimize;self.restart_strategy=restart;self.seed=seed
  self.binary_edges=[];self.scan={};self.binary_visits=0;self.long_scans=0;self.removed_literals=0;self.lbd_short=0.;self.lbd_long=0.;self.last_restart_conflicts=0
  super().__init__(*args,**kwargs)
  self.binary_edges=[[] for _ in self.watches];self.optimized=True
  if binary and self.root_conflict is None:
   for i,c in enumerate(self.clauses):
    if len(c)==2 and not self.tautological[i] and not any(self.val(l)==1 for l in c):self.add_binary(i)
   self.watches=[[ci for ci in w if len(self.clauses[ci])!=2] for w in self.watches]
  if seed:
   rng=random.Random(seed)
   for v in range(1,self.n+1):self.activity[v]+=rng.random()*1e-5
   self.heap=[(-self.activity[v],v) for v in range(1,self.n+1) if not self.values[v]];heapq.heapify(self.heap)
 def add_binary(self,ci):
  a,b=self.clauses[ci];self.binary_edges[self.idx(-a)].append((b,ci));self.binary_edges[self.idx(-b)].append((a,ci))
 def attach(self,ci):
  if self.optimized and self.binary_enabled and len(self.clauses[ci])==2:self.add_binary(ci)
  else:super().attach(ci)
 def propagate(self):
  if not self.optimized:return super().propagate()
  while self.qhead<len(self.trail):
   p=self.trail[self.qhead];self.qhead+=1;self.propagations+=1
   if self.binary_enabled:
    for q,ci in self.binary_edges[self.idx(p)]:
     self.binary_visits+=1
     if self.binary_visits%8192==0 and time.perf_counter()>=self.deadline:return -2
     value=self.val(q)
     if value==-1:return ci
     if not value:assert self.enqueue(q,ci)
   w=self.watches[self.idx(-p)];j=0
   while j<len(w):
    self.inspections+=1
    if self.inspections%8192==0 and time.perf_counter()>=self.deadline:return -2
    ci=w[j];c=self.clauses[ci]
    if c[0]==-p:c[0],c[1]=c[1],c[0]
    assert c[1]==-p
    first=c[0]
    if self.val(first)==1:j+=1;continue
    replacement=-1;n=len(c)
    if self.circular and n>3:
     start=self.scan.get(ci,2)
     for offset in range(n-2):
      k=2+(start-2+offset)%(n-2);self.long_scans+=1
      if self.val(c[k])!=-1:replacement=k;self.scan[ci]=2+(k-1)%(n-2);break
    else:
     for k in range(2,n):
      self.long_scans+=1
      if self.val(c[k])!=-1:replacement=k;break
    if replacement>=0:
     c[1],c[replacement]=c[replacement],c[1];w[j]=w[-1];w.pop();self.watches[self.idx(c[1])].append(ci);continue
    j+=1
    if self.val(first)==-1:return ci
    assert self.enqueue(first,ci)
  return -1
 def analyze(self,conflict):
  learnt,level=super().analyze(conflict)
  if self.minimize and 2<len(learnt)<=60:
   attempts=0
   for literal in learnt[1:][:]:
    if self.reasons[abs(literal)]<0:continue
    attempts+=1
    if attempts>8:break
    candidate=[l for l in learnt if l!=literal]
    try:self.hint_chain(conflict,candidate)
    except AssertionError:continue
    learnt=candidate;self.removed_literals+=1
   if len(learnt)>1:
    k=max(range(1,len(learnt)),key=lambda i:self.levels[abs(learnt[i])]);learnt[1],learnt[k]=learnt[k],learnt[1];level=self.levels[abs(learnt[1])]
   else:level=0
  lbd=len({self.levels[abs(l)] for l in learnt});self.lbd_short=.2*lbd+.8*self.lbd_short;self.lbd_long=.02*lbd+.98*self.lbd_long
  return learnt,level
 def should_restart(self,at):
  if self.restart_strategy=='lbd':return self.conflicts-self.last_restart_conflicts>=100 and (self.lbd_short>1.25*self.lbd_long or self.conflicts-self.last_restart_conflicts>=2000)
  return self.conflicts>=at
 def next_restart(self):
  self.last_restart_conflicts=self.conflicts
  return self.conflicts+(100*luby(self.restarts+1) if self.restart_strategy=='luby' else int(100*1.5**min(self.restarts,10)))
 def finish(self,status,start):
  r=super().finish(status,start);r.update(binary_visits=self.binary_visits,long_literal_scans=self.long_scans,minimized_literals=self.removed_literals,restart_strategy=self.restart_strategy,binary_enabled=self.binary_enabled,circular=self.circular,minimize=self.minimize,seed=self.seed);return r

 def solve(self,seconds=30,max_conflicts=100000):
  if self.used:raise ValueError('Solver objects are single-use; checkpoint clauses/proof then construct anew')
  self.used=True
  start=time.perf_counter();self.deadline=start+seconds
  if self.root_conflict is not None:
   self.proof.append({'clause':[],'hints':self.hint_chain(self.root_conflict,[])});return self.finish('UNSAT',start)
  restart_at=100
  while True:
   if time.perf_counter()>=self.deadline or self.conflicts>=max_conflicts:return self.finish('UNKNOWN',start)
   conflict=self.propagate()
   if conflict==-2:return self.finish('UNKNOWN',start)
   if conflict>=0:
    self.conflicts+=1
    if not self.limits:
     self.proof.append({'clause':[],'hints':self.hint_chain(conflict,[])});return self.finish('UNSAT',start)
    learnt,level=self.analyze(conflict);hints=self.hint_chain(conflict,learnt);self.proof.append({'clause':learnt[:],'hints':hints})
    self.backtrack(level);ci=len(self.clauses);self.clauses.append(learnt)
    if len(learnt)>1:self.attach(ci)
    assert self.enqueue(learnt[0],ci)
    self.increment/=0.95
    if self.increment>1e100:
     self.activity=[x*1e-100 for x in self.activity];self.increment*=1e-100;self.heap=[(-self.activity[v],v) for v in range(1,self.n+1) if not self.values[v]];heapq.heapify(self.heap)
    if len(self.heap)>20*self.n+1000:self.heap=[(-self.activity[v],v) for v in range(1,self.n+1) if not self.values[v]];heapq.heapify(self.heap)
   else:
    if self.should_restart(restart_at) and self.limits:
     self.backtrack(0);self.restarts+=1;restart_at=self.next_restart();continue
    v=self.choose()
    if not v:return self.finish('SAT',start)
    self.decisions+=1;self.limits.append(len(self.trail));assert self.enqueue(v*self.phase[v],-1)
