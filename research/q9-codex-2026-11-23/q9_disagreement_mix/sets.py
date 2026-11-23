from pathlib import Path
import random,json
from check import verify
D=Path(__file__).resolve().parent;R=D.parent
words=(D/'two_banks189.words').read_text().split()
sides=[]; seen=set()
for i,w in enumerate(words):
    p=verify(w)
    for side in [0,1]:
        S=sorted(x^(1 if side else 0) for x in p[side::2])
        assert len(S)==95 and all(v.bit_count()%2==0 for v in S)
        if tuple(S) not in seen:
            seen.add(tuple(S));sides.append((i,side,S))
rng=random.Random(745613);rng.shuffle(sides)
(D/'unique_sides.in').write_text(''.join('-1 -1 '+' '.join(map(str,S))+'\n' for _,_,S in sides))
(D/'unique_sides.json').write_text(json.dumps([(i,c) for i,c,_ in sides]))
with (D/'parity_control.in').open('w') as f:
    for w in (R/'q9_far189_spring_20261121/comparison191.words').read_text().split()[:10]:
        p=verify(w)[:-1];minor=set(p[1::2]);assert len(minor)==95
        missing=rng.sample(sorted(minor),3);extra=rng.sample([x for x in range(512) if x.bit_count()%2 and x not in minor],2)
        s=sorted(minor-set(missing)|set(extra))
        print(*sorted(s.index(x) for x in extra),*s,file=f)
print('distinct placed sides',len(sides))
