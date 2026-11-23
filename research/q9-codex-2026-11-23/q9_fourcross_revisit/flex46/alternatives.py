from pathlib import Path
from itertools import permutations
from collections import Counter
import random,json
D=Path(__file__).resolve().parent;rows=json.loads((D/'cases.json').read_text())
r=rows[0];A=r['anchor'];N=[{v^1<<j for j in range(8)} for v in range(256)];free=set(range(256))-set(A)-set.union(*(N[v] for v in A));low={v for v in r['hint'] if v<256};S=set(r['short']);core=set(A);alt=[]
for x in sorted(free):
    for y in N[x]&free:
        for z in (N[y]&free)-{x}:
            for w in (N[z]&free)-{x,y}-N[x]:
                if x>=w:continue
                sh=[x,y,z,w];b=set(sh)|set.union(*(N[v] for v in sh))
                alt.append((len((low-S)&b),-len(S&set(sh)),sh))
alt.sort();print('candidate short segments',len(alt),flush=True)
with (D/'alt_inputs.dat').open('w') as f:
    for i,(_,__,s) in enumerate(alt):print(i,len(A),*A,len(s),*s,file=f)
