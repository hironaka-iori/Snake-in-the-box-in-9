"""Forward generalized totalizer for an ASSERTED signed positive-weight PB cap.
Not an equivalence gate: auxiliary outputs need not be unique. Assert [target].
SAT iff the weighted cap holds, with an explicit canonical extension below.
This module does not alter BinaryCNF.gates or its existing witness semantics.
"""
from collections import Counter

class GeneralizedTotalizer:
 def __init__(self,cnf,terms,cap,emit=True):
  if not isinstance(cap,int) or isinstance(cap,bool):raise ValueError('integer cap required')
  self.cnf=cnf;self.emit=emit;self.nodes=[];self.clauses_count=0;self.variables_count=0;self.base_nv=cnf.nv;self.original_cap=cap
  weights=Counter()
  for literal,weight in terms:
   if not isinstance(literal,int) or isinstance(literal,bool) or not 0<abs(literal)<=cnf.nv:raise ValueError('existing nonzero integer literal required')
   if not isinstance(weight,int) or isinstance(weight,bool) or weight<0:raise ValueError('nonnegative integer weights required')
   if weight:weights[literal]+=weight
  self.offset=weights.pop(cnf.one,0);weights.pop(-cnf.one,None)
  for v in sorted({abs(l) for l in weights}):
   common=min(weights.get(v,0),weights.get(-v,0));self.offset+=common
   if common:weights[v]-=common;weights[-v]-=common
  terms=sorted(((l,w) for l,w in weights.items() if w),key=lambda t:(t[1],t[0]));self.normalized_terms=terms;self.cap=cap-self.offset
  self.maximum=sum(w for _,w in terms)
  if self.cap<0:self.target=-cnf.one;self.root=None;return
  if self.cap>=self.maximum:self.target=cnf.one;self.root=None;return
  self.K=self.cap+1;level=[]
  for literal,weight in terms:
   key=min(weight,self.K);self.nodes.append({'literal':literal,'weight':key,'thresholds':{key:literal}});level.append(len(self.nodes)-1)
  while len(level)>1:
   nxt=[]
   for i in range(0,len(level)-1,2):nxt.append(self._merge(level[i],level[i+1]))
   if len(level)%2:nxt.append(level[-1])
   level=nxt
  self.root=level[0];self.target=-self.nodes[self.root]['thresholds'][self.K]
 def _clause(self,literals):
  self.clauses_count+=1
  if self.emit:self.cnf.clauses.append(literals)
 def _merge(self,left,right):
  A=self.nodes[left]['thresholds'];B=self.nodes[right]['thresholds'];K=self.K
  sums=set(A)|set(B)
  sums.update(min(a+b,K) for a in A if a<K for b in B if b<K)
  out={s:self.cnf.fresh() for s in sorted(sums)};self.variables_count+=len(out)
  for s,literal in A.items():self._clause([-literal,out[s]])
  for s,literal in B.items():self._clause([-literal,out[s]])
  for a,la in A.items():
   if a==K:continue # unary overflow implication already suffices
   for b,lb in B.items():
    if b==K:continue
    self._clause([-la,-lb,out[min(a+b,K)]])
  self.nodes.append({'left':left,'right':right,'thresholds':out});return len(self.nodes)-1
 def extend(self,assignment):
  """Canonical threshold extension; call AFTER ordinary CNF.witness(inputs).
  Input literal values must already be present, including geometry gate values.
  This helper adds precisely the GT auxiliary values and does not modify inputs.
  """
  if not self.emit:raise ValueError('an estimate-only totalizer cannot supply a CNF witness')
  a=dict(assignment);scores=[]
  for node in self.nodes:
   if 'literal' in node:
    lit=node['literal'];score=node['weight'] if a[abs(lit)]==(lit>0) else 0
   else:
    score=min(self.K,scores[node['left']]+scores[node['right']])
    for threshold,var in node['thresholds'].items():a[var]=score>=threshold
   scores.append(score)
  return a
 def statistics(self):
  return {'normalized_terms':len(self.normalized_terms),'offset':self.offset,'remaining_cap':self.cap,'new_variables':self.variables_count,'new_clauses':self.clauses_count,'tree_nodes':len(self.nodes),'materialized':self.emit,'auxiliary_semantics':'forward thresholds; canonical extension exists, not unique in general'}

def leq_gt(cnf,terms,cap,emit=True):return GeneralizedTotalizer(cnf,terms,cap,emit)

