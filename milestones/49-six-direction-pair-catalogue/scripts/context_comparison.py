"""Compare a third counted centre with a longer two-centre context."""
from survey import p,HERE,canon
import json,itertools,contextlib,collections
cycle=json.loads((HERE/'data/analysis.json').read_text())['cycle'];answers=[]
with (HERE/'logs/context-comparison.txt').open('w') as log:
 for length,arity in [(6,3),(8,2)]:
  queries={}
  for phase,row in enumerate(cycle):
   for start in range(9-length):
    ds=list(canon(row['directions'][start:start+length]));caps=row['counts'][start:start+length-1]
    for positions in itertools.combinations(range(1,length),arity):
     bound=tuple(caps[j-1] for j in positions);key=tuple(ds),positions,bound
     queries.setdefault(key,[]).append([phase,start])
  for i,(key,occurrences) in enumerate(queries.items()):
   ds,positions,bound=key;p.DIRS=list(ds);caps=[21]*(length-1)
   for j,v in zip(positions,bound):caps[j-1]=v
   name=f'context-{length}-{arity}-{i}'
   with contextlib.redirect_stdout(log):r=p.solve(name,caps,seconds=2)
   answers.append(dict(name=name,length=length,arity=arity,dirs=list(ds),positions=positions,caps=bound,occurrences=occurrences,status=r['status']))
  (HERE/'data/context-comparison.json').write_text(json.dumps(answers,indent=2)+'\n')
  sub=[r for r in answers if r['length']==length]
  print('Context',length,'centres',arity,'cases',len(sub),dict(collections.Counter(r['status'] for r in sub)),'excluded phases',sorted({ph for r in sub if r['status']=='UNSAT' for ph,st in r['occurrences']}),flush=True)
