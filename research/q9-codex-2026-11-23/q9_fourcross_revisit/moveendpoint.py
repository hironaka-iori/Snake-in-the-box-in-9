import sys
from pathlib import Path
from itertools import groupby
import localport
D=Path(__file__).resolve().parent
paths=[list(map(int,l.split()))[5:] for l in (D/'improved180.paths').read_text().splitlines()];goal=int(sys.argv[1]);budget=int(sys.argv[2]);name=sys.argv[3];rad=int(sys.argv[4]);nb=lambda v:{v^1<<j for j in range(9)}
for k,p in enumerate(paths):
    gs=[list(z) for _,z in groupby(p,lambda x:x>=256)];q,s=sorted([gs[1],gs[3]],key=len,reverse=True);old=set(p);high={v for v in old if v>=256}
    for side,ep in enumerate((p[0],p[-1])):
        for y in sorted(nb(ep)-old):
            if y<256:continue
            blockers=(nb(y)&old)-{ep}
            if not blockers or any(v<256 for v in blockers) or len(blockers)>3:continue
            pinned={v-256 for v in high if all((v^u).bit_count()>rad for u in blockers)}|{ep-256,y-256}
            forbidden={v-256 for v in nb(y)-{ep} if v>=256}
            localport.run(q,s,goal,-1 if goal%2 else y.bit_count()%2,budget,1,name,{v-256 for v in high},pinned,forbidden,y-256)
