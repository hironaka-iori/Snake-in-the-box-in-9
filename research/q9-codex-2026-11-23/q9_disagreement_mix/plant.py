from itertools import permutations
from pathlib import Path
R=Path(__file__).resolve().parent.parent
def points(w):
    p=[0]
    for d in w:p.append(p[-1]^(1<<int(d)))
    return p
def valid(q):
    if len(set(q))!=len(q):return False
    s=set(q)
    return all(sum((v^1<<i) in s for i in range(9))==1+(0<j<len(q)-1) for j,v in enumerate(q))
def shortcut(p,i):
    for L in (4,5,6,7,8):
        a,b=p[i],p[i+L]
        ds=[d for d in range(9) if (a^b)>>d&1]
        if len(ds)!=L-2:continue
        keep=set(p[:i]+p[i+L+1:])
        forbidden=keep|{v^1<<d for v in keep for d in range(9)}
        for order in permutations(ds):
            vs=[a]
            for d in order[:-1]:
                v=vs[-1]^(1<<d)
                if v in forbidden:break
                vs.append(v)
            else:
                q=p[:i]+vs+p[i+L:]
                if valid(q):return q
done=0
for w in (R/'q9_far189_spring_20261121/comparison191.words').read_text().split():
    p=points(w);a=None
    for i in range(3,len(p)-12):
        q=shortcut(p,i)
        if q is None:continue
        if a is None:a=q;start=i;continue
        if i>start+12:
            print(*a,*q,flush=True);done+=1;break
    if done==12:break
print('controls',done,file=__import__('sys').stderr)
assert done
