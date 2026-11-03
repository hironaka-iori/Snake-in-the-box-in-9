"""Check positions on saved cycles only; no full-graph optimisation."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/results.json'
j=json.loads(source.read_text()); target=(0,1,2,0,3,2)
def canon(ds):
 names={}
 return tuple(names.setdefault(x,len(names)) for x in ds)
rows=[]
for p in j['profiles']:
 for edge in p['cycle']:
  hits=[]
  for s in range(2):
   word=edge['directions'][s+2:s+8];counts=edge['counts'][s:s+5]
   for reverse in [False,True]:
    ds=word[::-1] if reverse else word
    cs=counts[::-1] if reverse else counts
    if canon(ds)!=target:continue
    exact=cs==[3,5,4,5,3]
    weak=cs[0]==3 and cs[2]==4 and cs[4]==3 and cs[1]<6 and cs[3]<6
    hits.append(dict(placement=s,reverse=reverse,original_directions=ds,counts=cs,exact_match=exact,weakened_match=weak))
  rows.append(dict(profile=p['profile'],edge=edge['edge'],matches=hits))
exact={r['edge'] for r in rows if r['profile']=='completed' and any(h['exact_match'] for h in r['matches'])}
weak={r['edge'] for r in rows if r['profile']=='completed' and any(h['weakened_match'] for h in r['matches'])}
assert exact==weak=={308566,3806548}
assert not any(h['exact_match'] or h['weakened_match'] for r in rows if r['profile']=='conditional_floor18' for h in r['matches'])
out=dict(status='PASS_SAVED_CYCLE_POSITION_CHECK',rows=rows,completed_exact_edges=sorted(exact),completed_weakened_edges=sorted(weak),
 conditional_profile_matched_edges=[],source_files_sha256={source.relative_to(R).as_posix():sha(source),Path(__file__).relative_to(R).as_posix():sha(Path(__file__))},
 scope='Only the saved five- and six-edge cycles were checked. Exact exclusion is native-replay verified with Lean pending; weakening also needs a checked semantic specialization. No recomputed graph minimum or upper bound is asserted.')
path=H/'data/saved-cycle-positions.json';assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['rows','source_files_sha256']}))
