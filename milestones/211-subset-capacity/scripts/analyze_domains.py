"""Extract subset-capacity witnesses from the actual transferred domain vectors."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
folder=H/'data/case-23'
state=json.loads((folder/'initial-state.json').read_bytes())
cap=json.loads((folder/'capacity-constraints.json').read_bytes())
clique=cap['clique']
def words(mask):return [u for u in range(64) if mask>>u&1]
def analyze(job):
 d=job['domains'];owner={}
 def augment(x,seenvars,seenwords):
  if x in seenvars:return False
  seenvars.add(x)
  for u in words(d[clique[x]]):
   if u in seenwords:continue
   seenwords.add(u)
   if u not in owner or augment(owner[u],seenvars,seenwords):
    owner[u]=x;return True
  return False
 def witness(indices):
  variables=[clique[x] for x in sorted(indices)]
  pool=sorted({u for x in variables for u in words(d[x])})
  removals=[{'variable':x,'words':sorted(set(words(d[x]))&set(pool))} for x in clique if x not in variables]
  removals=[r for r in removals if r['words']]
  return {'variables':variables,'pool':pool,'domains':[words(d[x]) for x in variables],
          'count':len(variables),'width':len(pool),'removals':removals}
 for x in range(32):
  seenvars=set();seenwords=set()
  if not augment(x,seenvars,seenwords):
   w=witness(seenvars)
   if not w['width']<w['count']:raise RuntimeError('No deficient witness')
   return {'id':job['id'],'kind':'DEFICIENT','witnesses':[w]}
 reach=[{x}|{owner[u] for u in words(d[clique[x]])} for x in range(32)]
 for k in range(32):
  for x in range(32):
   if k in reach[x]:reach[x]|=reach[k]
 unique={tuple(sorted(s)) for s in reach}
 witnesses=[]
 for s in sorted(unique):
  w=witness(s)
  if w['count']==w['width'] and w['removals']:witnesses.append(w)
 return {'id':job['id'],'kind':'TIGHT' if witnesses else 'NO_STATIC_DEDUCTION','witnesses':witnesses}
rows=[analyze(job) for job in state['frontier']]
result={'source_sha256':hashlib.sha256((folder/'initial-state.json').read_bytes()).hexdigest(),
 'scope':'Only the seven literal transferred vectors, before binary propagation; actual domain union witnesses.',
 'records':rows}
(H/'data/transferred-subsets.json').write_text(json.dumps(result,indent=2)+'\n')
for row in rows:print(row['id'],row['kind'],[(w['count'],w['width'],sum(len(x['words']) for x in w['removals'])) for w in row['witnesses']])
