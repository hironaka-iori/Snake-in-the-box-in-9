"""Test intervening counts in the surviving diagnostic cycle, without assuming extension."""
from pathlib import Path
import hashlib,itertools,json,sys,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census,canonical
DIRS=[0,1,2,3,4,2,0,3]

def solve(name,caps,seconds=8,joint=None):
 t=time.monotonic();W=window(DIRS);e=TaggedEncoding(W,[(0,v) for v in caps],radius=4)
 if joint:
  positions,cap=joint;lits=[]
  for j in positions:
   free=[d for d in range(9) if d not in (DIRS[j-1],DIRS[j])]
   lits.extend(-e.var[W[j]^(1<<a)^(1<<b)] for a,b in itertools.combinations(free,2))
  e.atmost(lits,cap,('ends',))
 status='UNKNOWN';cuts=[];selected=None;report=None
 with Cadical153(bootstrap_with=e.clauses) as solver:
  while time.monotonic()-t<seconds:
   solver.conf_budget(10000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   model=solver.get_model();S={v for v in e.ball if model[e.var[v]-1]>0}
   report=census(S,9,W[1:-1]);report.pop('degree')
   if report['cycles']:
    for c in report['cycles']:cuts.append(c);solver.add_clause([-e.var[v] for v in c])
   else:status='SAT';selected=sorted(S);break
 out=dict(name=name,directions=DIRS,caps=caps,joint=joint,status=status,selected=selected,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t,scope='Necessary radius-four local conditions; no new theorem until proof replay and geometric interpretation.')
 (HERE/'data'/f'{name}.json').write_text(json.dumps(out,indent=2)+'\n')
 print(name,status,report['alpha'] if selected else '',round(out['seconds'],2),flush=True)
 return out

if __name__=='__main__':
 (HERE/'data').mkdir(parents=True,exist_ok=True)
 graph=ROOT/'milestones/36-critical-cycle-consistency/data/cycle-graph.json'
 row=next(r for r in json.loads(graph.read_text())['runs'] if r['stage']=='after' and r['table']=='lower')
 cc=row['cycle'];j=18;ds=list(canonical(cc[j]['directions'][::-1]));caps=[cc[(j-k)%len(cc)]['alpha'] for k in range(7)]
 assert ds==DIRS and caps==[3,4,4,5,5,3,3]
 (HERE/'data/target.json').write_text(json.dumps(dict(source=graph.relative_to(ROOT).as_posix(),source_sha256=hashlib.sha256(graph.read_bytes()).hexdigest(),phase=j,reversed=True,directions=ds,counts=caps,cycle_mean=row['mean']),indent=2)+'\n')
 solve('pair-only',[3,21,21,21,21,21,3])
 solve('critical-caps',caps)
 for i in range(1,6):
  one=[3,21,21,21,21,21,3];one[i]=caps[i];solve(f'only-{i+1}',one)
 for i in range(1,6):
  relaxed=caps.copy();relaxed[i]=21;solve(f'omit-{i+1}',relaxed)
 for cap in [15,18,20,21,22,23]:solve(f'middle-sum-{cap}',[3,21,21,21,21,21,3],joint=(list(range(2,7)),cap))
