from pathlib import Path
from collections import Counter
import sys
found=set()
for fn in sys.argv[1:]:
    for row in Path(fn).read_text().splitlines():
        c=row.split()
        if c[0] not in ('BEST','WIT','SEED'):continue
        p=list(map(int,c[5:] if c[0]=='BEST' and len(c[2])==15 else c[2:]))
        if len(p)<80:continue
        b=[]
        for x in p:
            if not b or b[-1][-1]>>5!=x>>5:b.append([])
            b[-1].append(x)
        for i in range(len(b)-7):
            blocks=b[i:i+8]
            for v in [blocks,[seg[::-1] for seg in blocks[::-1]]]:
                if sum(map(len,v))<86:continue
                inner=[[x%32 for x in s] for s in v]
                root=inner[0][0];data=[]
                for l in inner:
                    m=sum(1<<(x^root) for x in l);data.extend((m,l[-1]^root))
                found.add(tuple(data))
for a in sorted(found):print(*a)
