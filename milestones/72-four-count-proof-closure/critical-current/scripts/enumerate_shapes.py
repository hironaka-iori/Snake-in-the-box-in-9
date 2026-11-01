"""Enumerate canonical induced six-transition paths, including reversal."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
def canon(w):
 d={};return tuple(d.setdefault(x,len(d)) for x in w)
paths=[]
def extend(ds,vs):
 if len(ds)==6:paths.append(tuple(ds));return
 for d in range(max(ds,default=-1)+2):
  q=vs[-1]^(1<<d)
  if q in vs or any((q^v).bit_count()==1 for v in vs[:-1]):continue
  extend(ds+[d],vs+[q])
extend([],[0]);shapes=sorted({min(w,canon(w[::-1])) for w in paths})
out=dict(oriented=[list(w) for w in paths],up_to_reversal=[list(w) for w in shapes],scope='Exhaustive restricted-growth direction words of length six for induced paths. At most six coordinates are used, within Q9.')
previous=json.loads((HERE/'data/all-six-direction-shapes.json').read_text())
assert previous['up_to_reversal']==out['up_to_reversal']
(HERE/'data/all-six-direction-shapes.json').write_text(json.dumps(out,indent=2)+'\n')
print('Oriented shapes',len(paths),'up to reversal',len(shapes))
