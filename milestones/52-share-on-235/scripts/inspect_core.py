"""Record which singleton-count bounds the native core actually uses."""
from pathlib import Path
import collections,gzip,json
HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/supported0_95.json').read_text())
z=json.loads(gzip.decompress((HERE/'certificates/supported0_95.meanings.json.gz').read_bytes()))
counts=collections.Counter();bounds=collections.Counter()
for j in r['source_original_clause_ids']:
 t=z['tags'][j-1]
 if t[0]=='old' and t[1][0] in ['first','zero','mono','step','over']:
  ci=t[1][1];kind=str(z['ctrs'][ci][2]);counts[kind]+=1
  if t[1][0]=='over':bounds[kind]+=1
out=dict(counter_clause_counts=dict(counts),bound_clause_counts=dict(bounds),unused_singleton_positions_zero_based=[1,4],scope='Core inspection suggests removing the count restrictions at the second and fifth centres. The current theorem retains them; changing the bound list requires an adjusted counter interpretation and another Lean check.')
(HERE/'data/core-dependencies.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
