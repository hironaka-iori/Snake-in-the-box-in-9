from pathlib import Path
import hashlib,itertools,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/197-symmetry-placement/data/placements-all.json';case=json.loads(source.read_bytes())['rows'][4147]
def h(v):return sum(((v>>i)&1)<<case['permutation'][i] for i in range(7))^case['translation']
N={v:set([v^(1<<k) for k in range(7)]+[h(v)]) for v in range(128)}
triangles=[list(t) for t in itertools.combinations(range(128),3) if all(v in N[u] for u,v in itertools.combinations(t,2))]
cliques=[]
for v in range(128):
 if ((v>>1)&1)^((v>>4)&1)==1 and ((v>>3)&1)^((v>>6)&1)==1:
  c=sorted([v,v^4,v^32,v^36])
  if c not in cliques:cliques.append(c)
assert len(triangles)==32 and len(cliques)==8
assert set(map(tuple,triangles))=={t for c in cliques for t in itertools.combinations(c,3)}
assert all(h(v^1)==(h(v)^1) for v in range(128))
seed=json.loads((R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json').read_bytes())['7']['vertices']
contacts=[(i,j) for i in range(51) for j in range(i+2,51) if seed[j] in N[seed[i]]];assert contacts==[(4,38)]
out=dict(cliques=cliques,triangles=triangles,case=case,contact_positions=[4,38],contact_vertices=[seed[4],seed[38]],seed_clique_occupancy=[sum(v in seed for v in c) for c in cliques],seed=seed,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact triangle and K4 census of the fixed row4147 quotient; not a global snake bound.')
dest=H/'data/structure.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['cliques','contact_vertices','seed_clique_occupancy']}))
