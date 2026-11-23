from pathlib import Path
from itertools import combinations
import json
D=Path(__file__).resolve().parent
hosts=[set(map(int,l.split())) for l in Path('q8_all_191_positive.hosts').read_text().splitlines()]
paths=json.loads((D/'nine_witnesses.json').read_text())
dirs=[(1<<i,1<<j) for i,j in combinations(range(8),2)]
def block(x,axes):
    a,b=axes;return {v for u in (x,x^a,x^b,x^a^b) for v in (u,u^256)}
for row,H in enumerate(hosts):
    cross=sorted((H&set(range(256)))&{x-256 for x in H if x>=256});assert len(cross)==2
    tips=set()
    for w in paths:
        if w['host']==row:
            seq=w['vertices'];tips.update((seq[0]&255,seq[-1]&255))
    pairs=[(cross[0],cross[1],'cross')]+[(a,b,'tip') for a in cross for b in sorted(tips) if a!=b]
    unique=set()
    for a,b,label in pairs:
        for i,d in enumerate(dirs):
            for j,f in enumerate(dirs):
                if label=='tip' and (j-i)%7:continue
                ext=tuple(sorted((block(a,d)|block(b,f))-H))
                if len(ext)<4 or ext in unique:continue
                unique.add(ext);print('CASE',row,0,'outside',*ext)

