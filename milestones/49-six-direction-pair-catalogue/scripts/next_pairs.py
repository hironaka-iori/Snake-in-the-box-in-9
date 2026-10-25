"""Test all pair caps actually encountered on six-direction pieces of the new cycle."""
from survey import p,HERE,canon
import json,itertools,contextlib
cycle=json.loads((HERE/'data/analysis.json').read_text())['cycle'];queries={}
for phase,row in enumerate(cycle):
 for start in range(3):
  ds=list(canon(row['directions'][start:start+6]));caps=row['counts'][start:start+5]
  for a,b in itertools.combinations(range(1,6),2):
   u,v=caps[a-1],caps[b-1]
   key=tuple(ds),a,b,u,v
   queries.setdefault(key,[]).append([phase,start])
answers=[]
with (HERE/'logs/next-pairs.txt').open('w') as log:
 for i,(key,occurrences) in enumerate(queries.items()):
  ds,a,b,u,v=key;p.DIRS=list(ds);caps=[21]*5;caps[a-1]=u;caps[b-1]=v
  with contextlib.redirect_stdout(log):r=p.solve(f'next-pair-{i}',caps,seconds=2)
  answers.append(dict(name=f'next-pair-{i}',dirs=list(ds),positions=[a,b],caps=[u,v],occurrences=occurrences,status=r['status']))
 (HERE/'data/next-pairs.json').write_text(json.dumps(answers,indent=2)+'\n')
print('Scouted',len(answers),'distinct pair queries; UNSAT',sum(r['status']=='UNSAT' for r in answers),'UNKNOWN',sum(r['status']=='UNKNOWN' for r in answers),flush=True)
print('Excluded phases',sorted({phase for r in answers if r['status']=='UNSAT' for phase,start in r['occurrences']}),flush=True)
