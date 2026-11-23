import json,itertools
from collections import Counter
from pathlib import Path
from search_q9_wynn_plateau import WYNN, verify
import sys
root=Path(sys.argv[1]).parent.parent
bank=[r["vertex_sequence"] for r in json.loads((root/"work/bank9.json").read_text())]
if len(sys.argv)>2:
 import csv
 with Path(sys.argv[2]).open() as f:
  for row in csv.DictReader(f):
   path=list(map(int,row["vertices"].split()))
   if len(path)!=191 or not verify(path):
    raise ValueError("Invalid nine-dimensional 190-edge seed")
   bank.append(path)
w=[0]
for s in WYNN:w.append(w[-1]^(1<<int(s)))
bank += [w,json.loads((root/"outputs/snake8_witness.json").read_text())["vertex_sequence"]]
def norm(v):
 labels={};return bytes(labels.setdefault(u^w,len(labels)) for u,w in zip(v,v[1:]))
dimension=7 if "--level-seven" in sys.argv[3:] else 8
min_edges,max_edges=(46,50) if dimension==7 else (93,98)
arms=set()
for snake in bank:
 for start in range(len(snake)-min_edges+1):
  for k in range(min_edges,min(max_edges,len(snake)-start-1)+1):
   z=snake[start:start+k+1];code=norm(z)
   if max(code)<dimension:arms.update((code,norm(z[::-1])))

def variations(code):
 p=[0]
 for d in code:p.append(p[-1]^(1<<d))
 used=set(p)
 cand=[]
 for i in range(1,len(p)-1):
  x=p[i-1]^p[i]^p[i+1]
  if x in used:continue
  if sum((x^(1<<d)) in used for d in range(dimension))==2:
   cand.append(p[:i]+[x]+p[i+1:])
 for q in (p,p[::-1]):
  used=set(q[:-1])
  for d in range(dimension):
   x=q[-2]^(1<<d)
   if x in used or sum((x^(1<<e)) in used for e in range(dimension))!=1:continue
   cand.append(q[:-1]+[x])
 for q in cand:
  yield norm(q)
  yield norm(q[::-1])
extra={v for c in arms for v in variations(c)}
for arm in sorted(extra|arms): print("".join(map(str,arm)))
