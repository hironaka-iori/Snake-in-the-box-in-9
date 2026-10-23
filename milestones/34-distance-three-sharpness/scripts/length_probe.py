"""Ask whether a sharp pair can coexist with a 192-edge snake."""
import json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/33-distance-three-singletons/scripts'))
from certify import TaggedEncoding,window,candidates,Cadical153,census,joint_literals,BOUNDS,prior
from pysat.card import CardEnc,EncType
for i,cap in ((0,10),(1,9)):
 ds=candidates()[i]['dirs'];W=window(ds);e=TaggedEncoding(W,BOUNDS,radius=9);e.atmost(joint_literals(e,W),cap,('ends',))
 card=CardEnc.atleast(lits=list(e.var.values()),bound=193,top_id=e.nv,encoding=EncType.cardnetwrk)
 cuts=[];status='UNKNOWN';selected=None;report=None;t=time.monotonic();models=0
 with Cadical153(bootstrap_with=e.clauses+card.clauses) as solver:
  seed=json.loads((HERE/f'data/witness-{i}.json').read_text());S0=set(seed['vertex_sequence']);solver.set_phases([v if w in S0 else -v for w,v in e.var.items()])
  while time.monotonic()-t<30:
   solver.conf_budget(3000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   models+=1;m=solver.get_model();S={v for v in e.ball if m[e.var[v]-1]>0};r=census(S,9,W[1:-1]);r.pop('degree');assert len(S)>=193
   if not r['cycles']:
    assert len(prior.components(S))==1
    status='SAT';selected=sorted(S);report=r;break
   for cc in r['cycles']:
    prior.check_cut(cc);solver.add_clause([-e.var[v] for v in cc]);cuts.append(cc)
 out=dict(case=i,dirs=ds,cap=cap,minimum_vertices=193,status=status,seconds=time.monotonic()-t,models=models,cycle_cuts=cuts,selected=selected,census=report,
  scope='Full-cube sharp-pair length test. UNKNOWN is inconclusive; UNSAT would remain solver-only.')
 (HERE/f'data/length-192-case-{i}.json').write_text(json.dumps(out,indent=2)+'\n')
 print(i,status,'models',models,'cuts',len(cuts),'selected',None if selected is None else len(selected),flush=True)
