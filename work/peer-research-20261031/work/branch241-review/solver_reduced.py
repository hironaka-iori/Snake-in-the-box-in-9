"""Proof-preserving search-only deactivation of VERIFIED learned clauses.
No proof clause/ID is removed. Only watch entries are deactivated. Experimental.
The safe constructor takes static axioms and an RUP prefix, never a bare boundary.
"""
from solver_plus import Solver as Parent
from rup_check import check

class Solver(Parent):
 def __init__(self,static_clauses,checked_prefix=(),*,reduction_interval=500,min_candidates=200,keep_fraction=.5,**kwargs):
  if reduction_interval<1 or min_candidates<1 or not 0<keep_fraction<1:raise ValueError('invalid reduction policy')
  static=[list(c) for c in static_clauses];prefix=list(checked_prefix)
  self.prefix_check=check(static,prefix,require_empty=False)
  self.reducible_from=len(static);self.inactive=set();self.reduction_rounds=0;self.deactivation_audit=[]
  self.reduction_interval=reduction_interval;self.min_candidates=min_candidates;self.keep_fraction=keep_fraction
  super().__init__(static+[list(p['clause']) for p in prefix],**kwargs)
 def reduce_database(self,exclude=()):
  """Call only outside propagate; conflict analysis supplies its conflict ID."""
  locked={r for v,r in enumerate(self.reasons) if self.values[v] and r>=0};protected=locked|set(exclude)
  watched={i for row in self.watches for i in row}
  candidates=[i for i in watched if i>=self.reducible_from and i not in self.inactive and i not in protected and len(self.clauses[i])>2]
  if len(candidates)<self.min_candidates:return 0
  candidates.sort(key=lambda i:(len(self.clauses[i]),-i),reverse=True)
  count=max(1,int(len(candidates)*(1-self.keep_fraction)));selected=candidates[:count]
  assert all(i>=self.reducible_from and i not in locked and len(self.clauses[i])>2 for i in selected)
  self.inactive.update(selected)
  self.watches=[[i for i in row if i not in self.inactive] for row in self.watches]
  self.reduction_rounds+=1;self.deactivation_audit.append({'ids_zero_based':selected,'locked_at_reduction':sorted(locked),'excluded':sorted(exclude)})
  return count
 def analyze(self,conflict):
  if self.conflicts%self.reduction_interval==0:self.reduce_database(exclude=(conflict,))
  return super().analyze(conflict)
 def finish(self,status,start):
  result=super().finish(status,start);result.update(search_deactivated_clauses=len(self.inactive),reduction_rounds=self.reduction_rounds,static_clause_boundary=self.reducible_from,proof_database_clause_count=len(self.clauses));return result

