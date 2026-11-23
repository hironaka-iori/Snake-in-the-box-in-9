from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent
R=D.parent
def norm(s):
    m={}
    return ''.join(str(m.setdefault(c,len(m))) for c in s)
def canon(s):return min(norm(s),norm(s[::-1]))
def walk(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def inspect(p):
    return [(i,j) for j,y in enumerate(p) for i,x in enumerate(p[:j]) if x==y or (((x^y).bit_count()==1)!=(i+1==j))]
def slices(ws):return {canon(w[i:i+95]) for w in ws for i in range(len(w)-94)}
old=slices((R/'q8_catalogue_96_98.words').read_text().split())
fresh=slices((R/'q9_fresh_mother_lifts_20261120/q8_novel1626_95_20.words').read_text().split())
seed=set()
for l in (D/'short_seeds.txt').read_text().splitlines():
    n,m,*v=map(int,l.split())
    for p in (v[:n],v[n:]):
        w=''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
        seed.update(slices([w]))
bank=sorted(old|fresh|seed)
assert all(len(w)==95 and not inspect(walk(w)) for w in bank)
(D/'short95.words').write_text('\n'.join(bank)+'\n')
print(json.dumps({'catalogue_slices':len(old),'new_source':len(fresh),'short_seed_arms':len(seed),'union':len(bank),'outside_historical_slices':len(set(bank)-old)}))
