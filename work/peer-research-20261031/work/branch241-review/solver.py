"""Small, dependency-free CDCL with watched literals and checkable RUP hints.
Research tool, not Lean or a replacement for production CaDiCaL. No clause deletion.
"""
import heapq,time
class Solver:
 def __init__(self,clauses,nvars=None,primary=(),phase_true=()):
  self.clauses=[list(dict.fromkeys(c)) for c in clauses]
  if any(not isinstance(l,int) or isinstance(l,bool) or l==0 for c in self.clauses for l in c):raise ValueError('nonzero integer literals required')
  self.used=False
  self.tautological=[any(-l in seen for l in seen) for seen in map(set,self.clauses)]
  self.original_count=len(self.clauses);self.n=max([abs(l) for c in self.clauses for l in c]+[nvars or 0]);self.primary=set(primary)
  self.watches=[[] for _ in range(2*(self.n+1)+2)]
  self.values=[0]*(self.n+1);self.levels=[0]*(self.n+1);self.reasons=[-1]*(self.n+1);self.phase=[-1]*(self.n+1)
  for v in phase_true:self.phase[v]=1
  self.trail=[];self.limits=[];self.qhead=0;self.activity=[0.0]*(self.n+1);self.increment=1.0;self.proof=[];self.root_conflict=None
  self.decisions=self.conflicts=self.propagations=self.inspections=self.restarts=0
  for i,c in enumerate(self.clauses):
   if self.tautological[i]:continue
   if not c:self.root_conflict=i;continue
   for l in c:self.activity[abs(l)]+=1
   if len(c)==1:
    if not self.enqueue(c[0],i):self.root_conflict=i
   else:self.attach(i)
  # Complete permanent root propagation once, then rebuild only live watches.
  self.deadline=float('inf')
  if self.root_conflict is None:
   conflict=self.propagate()
   if conflict>=0:self.root_conflict=conflict
  self.root_satisfied_clauses=0;self.root_active_clauses=0
  if self.root_conflict is None:
   self.watches=[[] for _ in range(2*(self.n+1)+2)];self.activity=[0.0]*(self.n+1)
   for ci,c in enumerate(self.clauses):
    if self.tautological[ci] or any(self.val(l)==1 for l in c):self.root_satisfied_clauses+=1;continue
    free=[j for j,l in enumerate(c) if self.val(l)==0]
    assert len(free)>=2,'root UP was not at a fixpoint'
    chosen=set(free[:2]);c[:]=[c[j] for j in free[:2]]+[l for j,l in enumerate(c) if j not in chosen]
    self.attach(ci);self.root_active_clauses+=1
    for l in c:
     if self.val(l)==0:self.activity[abs(l)]+=1
  for v in self.primary:self.activity[v]*=4
  self.heap=[(-self.activity[v],v) for v in range(1,self.n+1)];heapq.heapify(self.heap)
 @staticmethod
 def idx(l):return 2*abs(l)+(l<0)
 def val(self,l):return self.values[abs(l)]*(1 if l>0 else -1)
 def enqueue(self,l,reason):
  v=abs(l);wanted=1 if l>0 else -1
  if self.values[v]:return self.values[v]==wanted
  self.values[v]=wanted;self.phase[v]=wanted;self.levels[v]=len(self.limits);self.reasons[v]=reason;self.trail.append(l);return True
 def attach(self,i):
  c=self.clauses[i];assert len(c)>=2
  self.watches[self.idx(c[0])].append(i);self.watches[self.idx(c[1])].append(i)
 def propagate(self):
  while self.qhead<len(self.trail):
   p=self.trail[self.qhead];self.qhead+=1;self.propagations+=1
   w=self.watches[self.idx(-p)];j=0
   while j<len(w):
    self.inspections+=1
    if self.inspections%8192==0 and time.perf_counter()>=self.deadline:return -2
    ci=w[j];c=self.clauses[ci]
    if c[0]==-p:c[0],c[1]=c[1],c[0]
    assert c[1]==-p
    first=c[0]
    if self.val(first)==1:j+=1;continue
    replacement=-1
    for k in range(2,len(c)):
     if self.val(c[k])!=-1:replacement=k;break
    if replacement>=0:
     c[1],c[replacement]=c[replacement],c[1];w[j]=w[-1];w.pop();self.watches[self.idx(c[1])].append(ci);continue
    j+=1
    if self.val(first)==-1:return ci
    assert self.enqueue(first,ci)
  return -1
 def bump(self,v):
  self.activity[v]+=self.increment;heapq.heappush(self.heap,(-self.activity[v],v))
 def analyze(self,conflict):
  seen=set();learnt=[0];pending=0;cursor=len(self.trail)-1;p=0;ci=conflict;level=len(self.limits)
  while True:
   for q in self.clauses[ci]:
    v=abs(q)
    if v==abs(p) or v in seen or not self.levels[v]:continue
    seen.add(v);self.bump(v)
    if self.levels[v]==level:pending+=1
    else:learnt.append(q)
   while abs(self.trail[cursor]) not in seen:cursor-=1
   p=self.trail[cursor];cursor-=1;seen.remove(abs(p));pending-=1
   if pending==0:learnt[0]=-p;break
   ci=self.reasons[abs(p)];assert ci>=0
  if len(learnt)==1:return learnt,0
  k=max(range(1,len(learnt)),key=lambda j:self.levels[abs(learnt[j])]);learnt[1],learnt[k]=learnt[k],learnt[1]
  return learnt,self.levels[abs(learnt[1])]
 def hint_chain(self,conflict,learnt):
  # Every reason's antecedents precede its pivot on the current trail.
  known={abs(l) for l in learnt};hints=[]
  stack=[(abs(l),False) for l in self.clauses[conflict] if abs(l) not in known]
  while stack:
   v,expanded=stack.pop()
   if v in known:continue
   ci=self.reasons[v]
   if ci<0:raise AssertionError(('unexplained decision in RUP chain',v,learnt))
   if expanded:known.add(v);hints.append(ci+1)
   else:
    stack.append((v,True))
    stack.extend((abs(l),False) for l in self.clauses[ci] if abs(l)!=v and abs(l) not in known)
  hints.append(conflict+1);return hints
 def backtrack(self,level):
  if len(self.limits)<=level:return
  stop=self.limits[level]
  for l in self.trail[stop:]:
   v=abs(l);self.values[v]=0;self.reasons[v]=-1;self.levels[v]=0;heapq.heappush(self.heap,(-self.activity[v],v))
  del self.trail[stop:];del self.limits[level:];self.qhead=len(self.trail)
 def choose(self):
  while self.heap:
   score,v=heapq.heappop(self.heap)
   if not self.values[v] and score==-self.activity[v]:return v
  return 0
 def finish(self,status,start):
  out={'status':status,'seconds':time.perf_counter()-start,'decisions':self.decisions,'conflicts':self.conflicts,'propagated':self.propagations,'watch_inspections':self.inspections,'restarts':self.restarts,'learned_clauses':len(self.proof),'root_satisfied_clauses':self.root_satisfied_clauses,'root_active_clauses':self.root_active_clauses}
  if status=='SAT':
   model=[v if self.values[v]>0 else -v for v in range(1,self.n+1)]
   assert all(any(self.val(l)==1 for l in c) for c in self.clauses)
   out['model']=model
  return out
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
    if self.conflicts>=restart_at and self.limits:
     self.backtrack(0);self.restarts+=1;restart_at=self.conflicts+int(100*1.5**min(self.restarts,10));continue
    v=self.choose()
    if not v:return self.finish('SAT',start)
    self.decisions+=1;self.limits.append(len(self.trail));assert self.enqueue(v*self.phase[v],-1)
