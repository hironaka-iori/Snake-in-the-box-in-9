"""Specialize the frozen joint model to extending the old terminal vertex."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
source=H/'scripts/coupled_search.py'
text=source.read_text(encoding='utf-8')
text=text.replace("ap.add_argument('--tag', required=True)","ap.add_argument('--tag', required=True)\nap.add_argument('--endpoint', type=int, required=True)")
text=text.replace("m.add(end[0] == 1)","assert a.endpoint < 256 and a.endpoint.bit_count() % 2 == 0\nassert (a.endpoint ^ seed[-1]).bit_count() == 1 and a.endpoint not in S\nm.add(end[a.endpoint] == 1)\nm.add(x[seed[-1]] == 1)\nm.add(end[0] == 1)")
text=text.replace("'All ports variable. Native feasibility search; no Lean infeasibility certificate.'", "'All ports variable. The old terminal vertex is retained internally and its specified neighbour is the new endpoint. Native feasibility search; no Lean infeasibility certificate.'")
dest=H/'scripts/endpoint_search.py'; assert not dest.exists(); dest.write_text(text,encoding='utf-8')
runner=(H/'scripts/run_search.py').read_text(encoding='utf-8').replace('scripts/coupled_search.py','scripts/endpoint_search.py')
(H/'scripts/run_endpoint.py').write_text(runner,encoding='utf-8')
raw=json.loads((H/'data/joint-d4.json').read_bytes()); seed=raw['seed']; S=set(seed)
rows=[]
for k in range(8):
    v=seed[-1]^(1<<k)
    blockers=[i for i,w in enumerate(seed[:-1]) if (v^w).bit_count()==1]
    rows.append(dict(endpoint=v,already_in_seed=v in S,eligible_new_endpoint=v not in S,old_neighbours=len(blockers)+1,mandatory_omitted_indices=blockers,mandatory_omitted_vertices=[seed[i] for i in blockers]))
rows.sort(key=lambda r:(len(r['mandatory_omitted_indices']),r['endpoint']))
(H/'data/endpoint-cases.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cases=rows,scope='The eight lower-face neighbours of88 include its old predecessor89. Only the seven eligible_new_endpoint rows are supported by endpoint_search.py. For a supported extension,88 remains and the chosen new endpoint has no other selected seed neighbour, so all listed blockers must be omitted. These cases do not cover arbitrary endpoint relocation.'),indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows),flush=True)
