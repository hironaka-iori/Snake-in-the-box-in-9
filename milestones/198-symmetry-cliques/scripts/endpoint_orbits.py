from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parents[1]
d=json.loads((H/'data/structure.json').read_bytes());c=d['case']
def h(v):return sum(((v>>i)&1)<<c['permutation'][i] for i in range(7))^c['translation']
def swap(v):return sum(((v>>i)&1)<<[0,3,2,1,6,5,4][i] for i in range(7))
N={v:set([v^(1<<i) for i in range(7)]+[h(v)]) for v in range(128)}
actions=[]
for flag in [0,1]:
 for t in range(128):
  if (t>>1&1)!=(t>>4&1) or (t>>3&1)!=(t>>6&1):continue
  image=[(swap(v) if flag else v)^t for v in range(128)]
  assert len(set(image))==128
  assert all({image[w] for w in N[v]}==N[image[v]] for v in range(128))
  actions.append(dict(swap_pairs=bool(flag),translation=t,images=image))
assert len(actions)==64
orbits=[sorted({a['images'][r] for a in actions}) for r in [10,2,0]]
assert [len(x) for x in orbits]==[32,64,32] and len(set(sum(orbits,[])))==128
triangle_vertices=set(sum(d['cliques'],[]));distance={v:0 for v in triangle_vertices}
for k in [1,2]:
 for v in range(128):
  if v not in distance and any(distance.get(w)==k-1 for w in N[v]):distance[v]=k
assert len(distance)==128 and all(all(distance[v]==i for v in row) for i,row in enumerate(orbits))
normalizers=[]
for v in range(128):
 root=[10,2,0][distance[v]];idx=next(i for i,a in enumerate(actions) if a['images'][v]==root)
 normalizers.append(dict(vertex=v,root=root,action=idx))
out=dict(actions=actions,orbits=orbits,normalizers=normalizers,triangle_distances=distance,source_sha256=hashlib.sha256((H/'data/structure.json').read_bytes()).hexdigest(),scope='A64-element subgroup suffices for endpoint representatives10,2,0. Distances to triangle vertices prove the three classes cannot be mixed even by larger graph automorphisms. No fixed-seed retention constraint is carried through this reduction.')
dest=H/'data/endpoint-orbits.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n')
print('ENDPOINT_ORBITS',[len(o) for o in orbits])
