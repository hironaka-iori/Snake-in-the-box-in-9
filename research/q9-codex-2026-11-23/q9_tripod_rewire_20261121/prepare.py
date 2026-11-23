from itertools import permutations
from pathlib import Path
from collections import Counter
import json
here=Path(__file__).resolve().parent
src=here.parent/'q9_facet_occupancy_search_20261121'
def normalize(s):
    d={};return ''.join(':' if x==':' else str(d.setdefault(x,len(d))) for x in s)
def word(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
bank={};freq=Counter()
for mode in ['warm','blend','cold']:
    for line in (src/(mode+'.log')).read_text().splitlines():
        z=line.split();idx=int(z[1]);m=sum(int(v)<<(64*j) for j,v in enumerate(z[12:20]))
        pts={v for v in range(512) if m>>v&1}
        if len(pts)!=193:continue
        adj={v:[v^(1<<d) for d in range(9) if v^(1<<d) in pts] for v in pts}
        if Counter(map(len,adj.values()))!={1:3,2:189,3:1}:continue
        center=next(v for v in pts if len(adj[v])==3);arms=[]
        for nxt in adj[center]:
            arm=[center,nxt]
            while len(adj[arm[-1]])==2:
                arm.append(next(x for x in adj[arm[-1]] if x!=arm[-2]))
            arms.append(arm)
        if len(set(sum(arms,[])))!=193:continue
        k=min(normalize(':'.join(word(a) for a in pp)) for pp in permutations(arms))
        bank.setdefault(k, [mode,idx,hex(m)]);freq[mode]+=1
out=sorted(bank)
(here/'arms.words').write_text('\n'.join(out)+'\n')
(here/'provenance.json').write_text(json.dumps(bank))
print(dict(freq),len(out),Counter(min(map(len,w.split(':'))) for w in out))
