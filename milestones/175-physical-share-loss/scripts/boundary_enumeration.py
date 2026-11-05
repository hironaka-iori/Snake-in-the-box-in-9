from itertools import product
from collections import Counter
import json
from pathlib import Path
h=Path(__file__).resolve().parents[1]
best=100; witnesses=[]; count=0
for x in product(range(1,7),repeat=7):
    if any((a==1 and b<4) or (b==1 and a<4) for a,b in zip(x,x[1:])):continue
    if any(x[i:i+3]==(2,2,2) for i in range(5)):continue
    count+=1;s=sum(x)
    if s<best:best=s;witnesses=[x]
    elif s==best:witnesses.append(x)
r={'scope':'Arithmetic strings only; no snake realizability claimed. Values above six cannot lower this minimum, because clipping to six preserves the constraints.','minimum':best,'minimizers':witnesses,'admissible_strings':count,'values_tested':[1,6]}
(h/'data/boundary-enumeration.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print(json.dumps(r))
