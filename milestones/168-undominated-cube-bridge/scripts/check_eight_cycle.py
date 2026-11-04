from itertools import product
import json
from pathlib import Path
rows=[]
for bits in product((0,1),repeat=4):
    degrees=[bits[i]+bits[(i-1)%4] for i in range(4)]
    admissible=min(degrees)>0 and not all(bits)
    endpoints=degrees.count(1)
    assert not admissible or endpoints>=2
    rows.append(dict(triples=bits,degrees=degrees,admissible=admissible,endpoints=endpoints))
p=Path(__file__).resolve().parents[1]/'data/eight-cycle-check.json'
p.write_text(json.dumps(dict(status='PASS',cases=16,admissible=sum(r['admissible'] for r in rows),rows=rows),indent=2)+'\n',encoding='utf-8')
print('PASS: all 16 selections; every admissible selection has at least two endpoints')
