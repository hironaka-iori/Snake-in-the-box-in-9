"""Derive direct lower-count clauses from the unchanged milestone-125 CNF."""
from pathlib import Path
from itertools import combinations
from collections import deque
import datetime,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];PRE=R/'milestones/125-critical-six-count'
for d in ['data','work','logs','audit','lean','build-isolated']:(H/d).mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
proposal=read(PRE/'data/next-encoding-task.json')
for name,digest in proposal['source_pins'].items():assert sha(PRE/name)==digest,name
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import window_from_dirs
source=PRE/'work/0120324-total22-positive/full.cnf'
case=read(PRE/'data/probes/0120324-total22-positive.json')
dirs=case['directions'];assert dirs==[0,1,2,0,3,2,4]
enc=TaggedEncoding(window_from_dirs(dirs),case['bounds'],radius=9)
corner_lists=[]
for i in range(1,7):
 c=enc.window[i];used={dirs[i-1],dirs[i]}
 corners=[c^(1<<a)^(1<<b) for a,b in combinations(range(9),2) if a not in used and b not in used]
 assert len(corners)==len(set(corners))==21;corner_lists.append(corners)
lits=sorted(-enc.var[v] for cs in corner_lists for v in cs)
assert len(lits)==126 and len(set(lits))==100
enc.atmost(lits,22,('unproved_sum',))
for cut in case['cycle_cuts']:enc.add([-enc.var[v] for v in cut],('cut',))
base=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
assert source.read_bytes()==base and len(enc.clauses)==106348 and enc.nv==7277
clauses=[tuple(c) for c in enc.clauses];N=len(clauses)
occ={};units=[]
for cid,c in enumerate(clauses,1):
 assert len(c)==len(set(c)) and not any(-x in c for x in c)
 if len(c)==1:units.append((cid,c[0]))
 for lit in c:occ.setdefault(lit,[]).append(cid)
def derive(clause):
 assigned=[0]*(enc.nv+1);queue=deque();hints=[]
 def value(lit):return assigned[abs(lit)]*(1 if lit>0 else -1)
 def put(lit,cid=None):
  if value(lit)>0:return False
  if cid is not None:hints.append(cid)
  if value(lit)<0:return True
  assigned[abs(lit)]=1 if lit>0 else -1;queue.append(lit);return False
 for lit in clause:assert not put(-lit)
 for cid,lit in units:
  if put(lit,cid):return hints
 while queue:
  lit=queue.popleft()
  for cid in occ.get(-lit,[]):
   c=clauses[cid-1]
   if any(value(x)>0 for x in c):continue
   rest=[x for x in c if value(x)==0]
   if not rest:hints.append(cid);return hints
   if len(rest)==1 and put(rest[0],cid):return hints
 raise AssertionError('Direct clause did not derive by unit propagation')
rows=[];start=time.monotonic()
for pos,(corners,bounds) in enumerate(zip(corner_lists,case['bounds']),1):
 k=bounds[0];assert k in [1,2,3]
 for omitted in combinations(range(21),k-1):
  clause=[-enc.var[v] for j,v in enumerate(corners) if j not in omitted]
  hints=derive(clause);cid=N+len(rows)+1
  assert all(0<h<=N for h in hints)
  rows.append(dict(id=cid,position=pos,lower=k,omitted_indices=list(omitted),clause=clause,hints=hints))
assert len(rows)==235 and len({tuple(x['clause']) for x in rows})==235
for row in rows:
 assigned={-x for x in row['clause']};conflict=False
 for cid in row['hints']:
  c=clauses[cid-1];assert not conflict and not any(x in assigned for x in c)
  rest=set(c)-{-x for x in assigned};assert len(rest)<=1
  if not rest:conflict=True
  else:assigned.add(next(iter(rest)))
 assert conflict
original=H/'work/original.cnf';prelude=H/'work/prelude.lrat';aug=H/'work/augmented.cnf'
assert not any(p.exists() for p in [original,prelude,aug])
original.write_bytes(base)
prelude.write_bytes(''.join(str(x['id'])+' '+' '.join(map(str,x['clause']))+' 0 '+' '.join(map(str,x['hints']))+' 0\n' for x in rows).encode())
aug.write_bytes((f'p cnf {enc.nv} {N+235}\n'+base.decode().split('\n',1)[1]+''.join(' '.join(map(str,x['clause']))+' 0\n' for x in rows)).encode())
(H/'data/direct-clauses.json').write_text(json.dumps(dict(rows=rows,corner_lists=corner_lists),indent=2)+'\n',encoding='utf-8')
pins={p.relative_to(R).as_posix():sha(p) for p in [source,PRE/'data/next-encoding-task.json',PRE/'data/probes/0120324-total22-positive.json',R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',R/'milestones/10-window-aggregate/scripts/wincert.py',PRE/'lean/ActualBounds125.lean',PRE/'data/ActualBounds125-audit.json']}
out=dict(status='PASS_235_DIRECT_CLAUSES_DERIVED_FROM_ORIGINAL_CNF',original_variables=enc.nv,original_clauses=N,derived_clauses=235,total_hints=sum(len(x['hints']) for x in rows),minimum_hints=min(len(x['hints']) for x in rows),maximum_hints=max(len(x['hints']) for x in rows),seconds=time.monotonic()-start,prelude_uses_original_inputs_only=True,original_sha256=sha(original),prelude_sha256=sha(prelude),augmented_sha256=sha(aug),data_sha256=sha(H/'data/direct-clauses.json'),script_sha256=sha(Path(__file__)),source_pins=pins,scope='Ordered unit-propagation derivations checked in Python. No contradiction of the complete formula or Lean proof of a new count floor.')
(H/'data/prelude.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
(H/'data/round-start.json').write_text(json.dumps(dict(base_commit='c57e9e87606cc879bfe860ad3af79c3e25276f0a',previous_goal_turn='PROGRESS',started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),prior_checkpoint_sha256=sha(R/'milestones/126-paper-revision/data/checkpoint.json'),paper_sha256=sha(R/'paper/snake9_research.tex'),goal_status='ACTIVE'),indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='source_pins'},indent=2))
