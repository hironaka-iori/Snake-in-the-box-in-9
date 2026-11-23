from pathlib import Path
from collections import Counter
from hashlib import sha256
import re,json
from verify import shape,valid,parse
r=Path(__file__).resolve().parent;workspace=Path('/Users/yichenzhan/Documents/ChatGPT/snake-in-the-box')
def inspect(f):
 rows=[parse(l) for l in f.read_text().splitlines()]
 for p in rows: valid(p)
 keys={shape(p) for p in rows}
 return keys,Counter(tuple(sorted(map(len,p))) for p in rows)
files=[r/f'{key}.pts' for key in 'ready distinct99 iso_positive ind101 ind100 cross101'.split()]
checks={};baseline={shape(parse(l)) for l in (workspace/'q8_dense_forest_bank_round2.pts').read_text().splitlines()}
for f in files:
 if not f.exists():continue
 shapes,bins=inspect(f);size=max((sum(pair) for pair in bins),default=0);checks[f.name]={'orbits':len(shapes),'counts_by_size':{'+'.join(map(str,pair)):v for pair,v in bins.items()},'max_vertices':size,'sha256':sha256(f.read_bytes()).hexdigest()}
 if size>=100:checks[f.name]['new_to_17']=len(shapes-baseline)
logs={f.stem:f.read_text().strip() for f in [r/f'{k}.log' for k in 'strict1 free1 strict2 free2 seam_all ed100 ed101 editthree grow99 regrow from_long from_97 sat100 sat101 sat3_100 sat3_101 merge_new iso3 edit99_100 seam99 iso_positive ind101 ind100 cross101'.split()] if f.exists() and f.stat().st_size}
info={'checked':checks,'seed_same_as_workspace':(r/'seed.pts').read_bytes()==(workspace/'q8_published_100_vertex_forest.pts').read_bytes(),'both_existing_17_orbit_banks_equal_to_ready':all(set(inspect(workspace/f'q8_dense_forest_bank_round{n}.pts')[0])==inspect(r/'ready.pts')[0] for n in (1,2)),'four_main_chain_proposals':sum(int(re.search(r'proposals (\d+)',logs[n])[1]) for n in 'strict1 free1 strict2 free2'.split()),'logs':logs}
(r/'audit.json').write_text(json.dumps(info,indent=2)+'\n')
print('audit saved',list(logs),checks.get('ind101.pts'),checks.get('cross101.pts'))

