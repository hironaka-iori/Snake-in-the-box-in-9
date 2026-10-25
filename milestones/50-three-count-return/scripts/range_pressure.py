"""Test a direct empty-square route against the existing completed 236 bound."""
from probe import p,HERE
from pysat.card import CardEnc,EncType
import itertools,json,time

def test(name,limit,vertices=None,seconds=30):
 W=[0,1,3];e=p.TaggedEncoding(W,[(0,21)],radius=9)
 clauses=list(e.clauses);top=e.nv;empty=[];squares=[]
 for a,b in itertools.combinations(range(9),2):
  for v in range(512):
   if v&(1<<a) or v&(1<<b):continue
   sq=[v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)];squares.append(sq)
   top+=1;z=top;empty.append(z)
   clauses.append([z]+[e.var[x] for x in sq])
   clauses.extend([[-z,-e.var[x]] for x in sq])
 bound=CardEnc.atmost(empty,bound=limit,top_id=top,encoding=EncType.cardnetwrk);top=bound.nv;clauses+=bound.clauses
 if vertices is not None:
  card=CardEnc.equals(list(e.var.values()),bound=vertices,top_id=top,encoding=EncType.cardnetwrk);top=card.nv;clauses+=card.clauses
 t=time.monotonic();status='UNKNOWN';cuts=[];selected=None
 with p.Cadical153(bootstrap_with=clauses) as solver:
  while time.monotonic()-t<seconds:
   solver.conf_budget(500);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   model=solver.get_model();S={v for v in range(512) if model[e.var[v]-1]>0}
   census=p.census(S,9,[1]);census.pop('degree')
   if census['cycles']:
    for cc in census['cycles']:solver.add_clause([-e.var[v] for v in cc]);cuts.append(cc)
   else:
    assert sum(not(set(sq)&S) for sq in squares)<=limit
    if vertices is not None:assert len(S)==vertices
    selected=sorted(S);status='SAT';break
 out=dict(name=name,status=status,empty_limit=limit,selected_vertices=vertices,variables=top,clauses=len(clauses),cycle_cuts=cuts,selected=selected,seconds=time.monotonic()-t,scope='Global necessary-condition solver test, with full acyclicity separation; no exclusion theorem until certificate replay and complete geometric interpretation.')
 (HERE/f'data/{name}.json').write_text(json.dumps(out,indent=2)+'\n')
 print(name,status,'seconds',round(out['seconds'],2),'cycles',len(cuts),flush=True)
if __name__=='__main__':
 test('empty18-at-237',18,237,seconds=30)
 test('empty18-universal',18,None,seconds=30)
