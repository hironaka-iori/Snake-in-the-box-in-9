"""Build repair seeds from exact 190-edge snakes and two additional steps."""
from collections import Counter
import gzip, random, sys
from pathlib import Path
base=Path("q9_dynamic_fold_20261120/reference190.words.gz")
seen={tuple(map(int,l.split())) for l in open("q9_onechord_minority_sets.txt")}
rng=random.Random(928602)
counts=Counter()
with gzip.open(base,"rt") as f:
    words=list(f)
rng.shuffle(words)
for word in words:
    p=[0]
    for c in word.strip():p.append(p[-1]^(1<<int(c)))
    used=set(p)
    assert len(used)==len(p)==191 and all(sum((v^(1<<d)) in used for d in range(9))==(1 if i in (0,190) else 2) for i,v in enumerate(p))
    for order in (p,p[::-1]):
        tip=order[-1]
        for a in range(9):
            x=tip^(1<<a)
            if x in used:continue
            for ends in (1,2):
                options=[]
                for b in range(9):
                    y=(x if ends==1 else order[0])^(1<<b)
                    if y in used or y==x:continue
                    chords=sum((x^(1<<d)) in used for d in range(9))-1+sum((y^(1<<d)) in used for d in range(9))-(ends==2)+((ends==2) and (x^y).bit_count()==1)
                    if chords<=6: options.append((chords,rng.random(),y))
                if not options:continue
                chords,_,y=min(options)
                walk=order+[x,y] if ends==1 else [y]+order+[x]
                key=tuple(sorted(walk[1::2]))
                if key in seen:continue
                seen.add(key);counts[chords]+=1
                print(*walk)
print(dict(sorted(counts.items())), file=sys.stderr)
