import json
from pathlib import Path
d=json.loads(Path("q8_single_cross_chords_20261120/minimum_chord_witnesses.json").read_text())
idx=0
for items in d.values():
 for item in items:
  p=item["witness"]["vertices"]
  assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
  j,=[i for i,(a,b) in enumerate(zip(p,p[1:])) if (a^b)==256]
  assert sorted((j,len(p)-2-j))==sorted(item["arms"])
  assert (p[j]^p[j+1])==256
  for t in range(192,len(p)):
   for k in range(len(p)-t):
    print(idx,t,j-k,*p[k:k+t+1])
    idx+=1
