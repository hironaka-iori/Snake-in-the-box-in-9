from pathlib import Path
from collections import Counter
import json
root=Path(__file__).resolve().parent
known=set((root/'all_near_registered.words').read_text().split())
def shape(s):
    def key(w):
        d={}
        return ''.join(d.setdefault(x,str(len(d))) for x in w)
    return min(key(s),key(s[::-1]))
def vertices(s):
    p=[0]
    for c in s:p.append(p[-1]^(1<<int(c)))
    return p
words=(root/'monotone_near.words').read_text().split()
out={}
for t in (192,195,196):
    win={shape(w[i:i+t]) for w in words for i in range(len(w)-t+1)}
    extra=win-{shape(w[i:i+t]) for w in known for i in range(len(w)-t+1)}
    with (root/f'monotone_{t}.pts').open('w') as f:
        for w in sorted(extra):print(*vertices(w),file=f)
    out[t]=(len(win),len(extra))
print(out)
