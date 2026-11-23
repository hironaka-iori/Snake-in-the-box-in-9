from pathlib import Path
from verify import parse,valid,shape
from collections import Counter
from sys import argv
r=Path(__file__).resolve().parent
shapes={};old=set()
for f in [Path('/tmp/q8_record_forests20.pts'),*r.glob('bank99_*.pts'),r/'merge_new.pts']:
 if not f.exists():continue
 for line in f.read_text().splitlines():
  p=parse(line)
  if sum(map(len,p))!=99:continue
  valid(p);k=shape(p)
  if f.name=='q8_record_forests20.pts':old.add(k)
  else:shapes[k]=line
subset={k:v for k,v in shapes.items() if k not in old}
with (r/'distinct99.pts').open('w') as f:
 for l in subset.values():print(l,file=f)
print('99 orbits',len(shapes),'new to 1101-donor bank',len(subset),'baseline orbits',len(old),'splits',Counter(tuple(sorted(map(len,parse(s)))) for s in subset.values()))

