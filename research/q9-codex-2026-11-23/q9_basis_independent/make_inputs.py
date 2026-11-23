from pathlib import Path
from random import Random
D=Path(__file__).resolve().parent;Q=D.parent/'q9_change_basis';bank=(D.parent/'q9_gap_generations/prior191.words').read_text().split();rng=Random(71943)
def pts(w):
    p=[0]
    for x in w:p.append(p[-1]^(1<<int(x)))
    return p
for name,words in [('full'+str(g),(Q/f'windows{g}.txt').read_text().split()) for g in [192,195,196]]+[('allbank',bank)]:
    with (D/(name+'.pts')).open('w') as f:
        for w in words:print(*pts(w),file=f)
with (D/'twoholes.pts').open('w') as f:
    for row,w in enumerate((Q/'windows192.txt').read_text().split()[:260]):
        p=pts(w);gone=rng.sample(range(len(p)),2);print(*(v for j,v in enumerate(p) if j not in gone),file=f)
with (D/'positive.pts').open('w') as f:
    for row,w in enumerate(bank[:24]):
        p=pts(w);axes=[1<<i for i in range(9)]
        for _ in range(40):
            a,b=rng.sample(range(9),2);axes[a]^=axes[b]
        original=[0]
        for x in w:original.append(original[-1]^axes[int(x)])
        if row%3==0:holes=[0,1]
        elif row%3==1:holes=[98,99]
        else:holes=rng.sample(range(3,188),2)
        p=[v for j,v in enumerate(original) if j not in holes];rng.shuffle(p);print(*p,file=f)
