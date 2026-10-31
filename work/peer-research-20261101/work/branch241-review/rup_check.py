"""Independent positive-hint RUP checker. Does not call the solver or search.
Each hint must be a unit clause under the negated proposed clause and prior hints,
and the last hint must be false. Clauses are only added; no deletion is supported.
"""
def check(clauses,proof,require_empty=True):
 db=[list(dict.fromkeys(c)) for c in clauses];steps=0;hints_checked=0
 for step in proof:
  clause=step['clause'];assignment={};contradiction=False
  for l in clause:
   v=abs(l);value=l<0
   if v in assignment and assignment[v]!=value:contradiction=True;break
   assignment[v]=value
  if contradiction:raise ValueError('tautological proof clauses are not accepted in this format')
  ids=step['hints']
  for pos,h in enumerate(ids):
   if not 1<=h<=len(db):raise ValueError(('invalid/premature hint',h))
   unresolved=set();satisfied=False
   for l in db[h-1]:
    value=assignment.get(abs(l))
    if value is None:unresolved.add(l)
    elif value==(l>0):satisfied=True;break
   if satisfied:raise ValueError(('hint is satisfied, not unit/false',steps,h))
   if not unresolved:
    if pos!=len(ids)-1:raise ValueError('hint chain continues after contradiction')
    contradiction=True
   elif len(unresolved)==1:
    l=next(iter(unresolved));assignment[abs(l)]=l>0
   else:raise ValueError(('hint not unit',steps,h))
   hints_checked+=1
  if not contradiction:raise ValueError(('no RUP contradiction',steps))
  db.append(list(dict.fromkeys(clause)));steps+=1
 if require_empty and (not proof or proof[-1]['clause']):raise ValueError('no final empty clause')
 return {'RUP_steps_checked':steps,'unit_hints_checked':hints_checked,'empty_clause_checked':bool(proof and not proof[-1]['clause'])}
