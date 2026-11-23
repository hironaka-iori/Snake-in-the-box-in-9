"""Create a true 191-edge test with two disjoint damage sites, then reconstruct."""
import json
from itertools import combinations
from run import ROOT,HERE,CUBE,inspect,regions,search
from search_q9_anchored_sets import search as mini

p=json.load(open(ROOT/'q9_explicit_q8_96_plus_94.json'))['vertices']
assert len(p)==192 and not inspect(p)
candidates=[]
for i in range(1,len(p)-1):
    v=p[i-1]^p[i]^p[i+1]
    if v in p:continue
    changed=p[:i]+[v]+p[i+1:]
    if len(inspect(changed))==1:candidates.append((i,v))
for (i,a),(j,b) in combinations(candidates,2):
    if abs(i-j)<16 or a==b:continue
    q=p.copy(); q[i]=a; q[j]=b
    chords=inspect(q)
    if len(chords)!=2 or len(set(sum((list(c) for c in chords),[])))!=4:continue
    for fixed,params in regions(q,chords):
        if a in fixed or b in fixed:continue
        st1,w1=search(set(fixed),set(q),191,12000,CUBE)
        st2,w2=mini(set(fixed),set(q),191,12000,at_least=True)
        for stat,w in [(st1,w1),(st2,w2)]:
            assert stat=='FOUND' and len(w)>=192 and not inspect(w) and fixed<=set(w)
        print(json.dumps(dict(changed=[i,j],chords=chords,params=params,anchors=len(fixed),cadical=w1,minicard=w2)))
        raise SystemExit
raise AssertionError('missing control')
