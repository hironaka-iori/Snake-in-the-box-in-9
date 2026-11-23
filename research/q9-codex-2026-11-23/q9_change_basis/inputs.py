from pathlib import Path
from random import Random
from itertools import chain
D=Path(__file__).resolve().parent;R=D.parent
def norm(s):
    def n(w):
        names={};return ''.join(names.setdefault(d,str(len(names))) for d in w)
    return min(n(s),n(s[::-1]))
def points(w):
    p=[0]
    for a in w:p.append(p[-1]^(1<<int(a)))
    return p
def main():
    bank=(R/'q9_gap_generations/prior191.words').read_text().split();near=(R/'q9_via_q10/monotone_near.words').read_text().split()
    rand=Random(8821)
    for n in [192,195,196]:
        allw={norm(w[i:i+n]) for w in near for i in range(len(w)-n+1)}
        v=sorted(w for w in allw if len(set(points(w)))==n+1);rand.shuffle(v)
        (D/f'windows{n}.txt').write_text(''.join(w+'\n' for w in v));print(n,len(v))
    for k in (4,5,6,7):
        rows=[]
        for w in bank[:4]:
            axes=list(range(9));rand.shuffle(axes);locked=axes[:k];extras=axes[k:]
            basis={a:1<<a for a in locked}
            for a in extras:basis[a]=(1<<a)^(1<<rand.choice(locked))
            p=[0]
            for a in w:p.append(p[-1]^basis[int(a)])
            rows.append('points '+' '.join(map(str,p)))
        (D/f'control{k}.txt').write_text('\n'.join(rows)+'\n')
if __name__=='__main__':main()
