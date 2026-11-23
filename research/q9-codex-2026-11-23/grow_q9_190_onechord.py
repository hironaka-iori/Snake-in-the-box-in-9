"""Find length-192 one-chord walks via square detours and end extensions of 190s."""
import csv
from pathlib import Path
from collections import Counter
from search_q9_wynn_plateau import canonical,NB,verify
import sys


def generators(p):
    used=set(p);ns=Counter(w for v in p for w in NB[v])
    for i,(u,v) in enumerate(zip(p,p[1:])):
        for d in range(9):
            a=u^(1<<d);b=v^(1<<d)
            if a not in used and b not in used and ns[a]==ns[b]==1:
                yield 'square',p[:i+1]+[a,b]+p[i+1:]
    for q in (p,p[::-1]):
        for a in NB[q[-1]]:
            if a in used or ns[a]>2:continue
            for right in (True,False):
                e=a if right else q[0]
                for b in NB[e]:
                    if b in used or b==a:continue
                    cost=ns[a]+ns[b]+int((a^b).bit_count()==1)-2
                    if cost<=1:yield 'endpoint',q+[a,b] if right else [b]+q+[a]


if __name__=='__main__':
    seen=set();counts=Counter()
    with open(sys.argv[1]) as f,open(sys.argv[2],'w') as out:
        for row in csv.DictReader(f):
            p=list(map(int,row['vertices'].split()));assert len(p)==191 and verify(p)
            for kind,q in generators(p):
                k=canonical(q)
                if k in seen:continue
                seen.add(k);counts[kind]+=1
                chords=[(i,j) for i,v in enumerate(q) for j in range(i+2,len(q)) if (v^q[j]).bit_count()==1]
                assert len(q)==len(set(q))==193 and len(chords)<=1
                if not chords:print('FOUND',*q,flush=True);raise SystemExit(0)
                print(*q,file=out)
    print('COUNT',dict(counts),'distinct',len(seen))
