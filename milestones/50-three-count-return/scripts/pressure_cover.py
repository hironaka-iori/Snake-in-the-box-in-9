"""Reduce the proof workload while retaining the improved potential certificate."""
from pathlib import Path
import gzip,json,sys,collections
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np;meta=json.loads((HERE/'data/model.json').read_text())
with np.load(HERE/'build/graph.npz') as z:a={k:z[k] for k in z.files}
pi=np.frombuffer(gzip.decompress((HERE/'excess-screen/data/potential.i64.gz').read_bytes()),dtype='<i8')
weight=168*a['count'].astype(np.int64)+24*a['demand']+42*a['share']
violations=np.flatnonzero((~a['excluded'])&(weight+pi[a['U']]-pi[a['V']]<644))
need=(644+pi[a['V'][violations]]-pi[a['U'][violations]]-168*a['count'][violations].astype(np.int64)-42*a['share'][violations].astype(np.int64)+23)//24
# Each rule is interpreted on a common seven-centre excess budget.
rows=[dict(r,kind='exclude') for r in json.loads((HERE/'data/critical-survey.json').read_text()) if r['status']=='UNSAT']
rows += [dict(r,kind='demand',required=r['excess_cap']+1) for r in json.loads((HERE/'data/excess-survey.json').read_text()) if r['status']=='UNSAT']
def matches(row,indices):
 covered=np.zeros(len(indices),dtype=bool);directions=a['direction'][indices];codes=a['count_code'][indices]
 for i,ds in enumerate(meta['extensions']):
  group=directions==i
  if not np.any(group):continue
  values=codes[group];ok=np.zeros(len(values),dtype=bool)
  for start in range(3):
   for rev in [False,True]:
    word=ds[start:start+6]
    if model.canon(word[::-1] if rev else word)!=tuple(row['directions']):continue
    hit=np.ones(len(values),dtype=bool)
    for j,c in enumerate(row['counts'],1):
     position=start+6-j if rev else start+j;v=values//6**(7-position)%6+1
     if c<6:hit&=v<=c
     elif row['kind']=='demand':hit&=v==6
    ok|=hit
  covered[group]=ok
 return covered
covers=[]
for row in rows:
 mask=matches(row,violations)
 if row['kind']=='demand':mask &= need<=row['required']
 covers.append(set(np.flatnonzero(mask).tolist()))
uncovered=set(range(len(violations)));chosen=[]
while uncovered:
 gains=[len(c&uncovered) if i not in chosen else 0 for i,c in enumerate(covers)]
 best=max(range(len(rows)),key=lambda i:gains[i]);assert gains[best]>0
 chosen.append(best);uncovered-=covers[best]
# Reverse deletion makes the greedy cover inclusion-minimal, not cardinality-optimal.
for i in chosen[::-1]:
 other=set().union(*(covers[j] for j in chosen if j!=i))
 if len(other)==len(violations):chosen.remove(i)
selected=[dict(rows[i],covered_violations=len(covers[i])) for i in chosen]
union=set().union(*(covers[i] for i in chosen));assert len(union)==len(violations)
# A second pass constructs the resulting graph and checks every retained edge.
ids=np.flatnonzero(~a['excluded']);excluded=a['excluded'].copy();demand=a['demand'].copy()
for row in selected:
 hits=ids[matches(row,ids)]
 if row['kind']=='exclude':excluded[hits]=True
 else:demand[hits]=np.maximum(demand[hits],row['required'])
keep=~excluded;newweight=168*a['count'][keep].astype(np.int64)+24*demand[keep]+42*a['share'][keep]
assert np.all(644+pi[a['V'][keep]]<=newweight+pi[a['U'][keep]])
out=dict(status='EXACT_FINITE_COVER_WITH_UNREPLAYED_PREMISES',candidate_rules=len(rows),violating_edges=len(violations),selected_rules=selected,selected_count=len(selected),types=dict(collections.Counter(r['kind'] for r in selected)),remaining_edges=int(keep.sum()),normalized_mean_lower_bound='23/6',potential_range=int(pi.max()-pi.min()),scope='All-edge integer potential verified after these selected rules. Their geometric premises still require Lean replay. Greedy inclusion-minimal cover, no claim of minimum certificate count or improved global bound.')
(HERE/'data/pressure-cover.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='selected_rules'},flush=True)
print('Selected',[(r['name'],r['kind']) for r in selected],flush=True)
