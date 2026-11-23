import json
from pathlib import Path
D=Path(__file__).resolve().parent
def rows(f):return map(json.loads,(D/f).read_text().splitlines())
sets={tuple(r[3]) for f in ('connected_wide.jsonl','mosaic.jsonl') for r in rows(f) if r[2]=='FOUND'}
(D/'resolved.sets').write_text(''.join('97 '+' '.join(map(str,a))+'\n' for a in sorted(sets)))
