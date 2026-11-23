from pathlib import Path
from collections import Counter
def gen(x,mask,w):
    if len(w)==15:yield w
    for d in range(4):
        y=x^(1<<d)
        if not mask>>y&1:yield from gen(y,mask|(1<<y),w+str(d))
def canon(w):
    def rel(x):
        a={};return ''.join(str(a.setdefault(d,len(a))) for d in x)
    return min(rel(w),rel(w[::-1]))
out=sorted({canon(w) for w in gen(0,1,'') if min(Counter(w).values())>=2})
assert len(out)==98
print('\n'.join(out))
