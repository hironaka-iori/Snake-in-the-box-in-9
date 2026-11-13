from pathlib import Path
import collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
dest=H/'data/low-overlap-maps.json';assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();p=json.loads(raw)['7']['vertices'];index={v:i for i,v in enumerate(p)}
rows=[];hist=collections.Counter();start=time.monotonic()
for perm in itertools.permutations(range(7)):
 images=[sum(((v>>k)&1)<<perm[k] for k in range(7)) for v in p];counts=[0]*128
 for u in p:
  for v in images:counts[u^v]+=1
 hist.update(counts)
 for t,c in enumerate(counts):
  if c>4:continue
  inv=[perm.index(i) for i in range(7)];it=sum(((t>>k)&1)<<inv[k] for k in range(7))
  rows.append(dict(permutation=list(perm),translation=t,intersection_count=c,collisions=[(index[v^t],j) for j,v in enumerate(images) if v^t in index],inverse=dict(permutation=inv,translation=it),involution=list(perm)==inv and t==it))
keys={(tuple(r['permutation']),r['translation']):i for i,r in enumerate(rows)}
for i,r in enumerate(rows):r['inverse_index']=keys[tuple(r['inverse']['permutation']),r['inverse']['translation']];r['representative']=min(i,r['inverse_index'])
prior=json.loads((R/'milestones/199-parent-diversity/data/all-isometries-published50.json').read_bytes())
assert dict(hist)=={int(k):v for k,v in prior['rows'][0]['intersection_histogram'].items()}
out=dict(status='COMPLETE',seconds=time.monotonic()-start,isometries=645120,rows=rows,representatives=sorted(set(r['representative'] for r in rows)),resource_gate=gate,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All cube isometries placing the published parent with at most4 intersection vertices. A coupled repair with at most4 omissions must start in this list by collisionCovered. Inverse maps represent equivalent ordered parent problems after swapping parents and applying the inverse isometry. Native catalogue completeness; no Lean replay.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(maps=len(rows),involutions=sum(r['involution'] for r in rows),representatives=out['representatives'],seconds=out['seconds'])),flush=True)
