"""Allow arbitrary new occupied vertices around Hamming-ball releases of a two-chord seed."""
from collections import Counter
from itertools import product
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT))
from retry_q9_six_cube_sites_cadical import search

CUBE=set(range(512))
def inspect(p):
    assert len(set(p))==len(p) and all(v in CUBE for v in p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return [(i,j) for j,b in enumerate(p) for i,a in enumerate(p[:max(j-1,0)]) if (a^b).bit_count()==1]

def regions(p,chords):
    for sides in product((0,1),repeat=2):
        centers=[p[pair[s]] for pair,s in zip(chords,sides)]
        for r1,r2 in [(2,2),(2,3),(3,2),(3,3),(2,4),(4,2),(3,4),(4,3),(4,4)]:
            for tipradius in (0,2):
                balls=list(zip(centers,(r1,r2)))+[(p[0],tipradius),(p[-1],tipradius)]
                fixed=frozenset(v for v in p if all((v^c).bit_count()>radius for c,radius in balls))
                yield fixed,[list(sides),r1,r2,tipradius]

def control():
    p=json.load(open(ROOT/'q9_explicit_q8_96_plus_94.json'))['vertices']
    assert len(p)==192 and not inspect(p)
    for i in range(1,len(p)-1):
        v=p[i-1]^p[i]^p[i+1]
        if v in p: continue
        q=p[:i]+[v]+p[i+1:]
        chords=inspect(q)
        if len(chords)!=2:continue
        for fixed,params in regions(q,chords):
            if v in fixed:continue
            st,w=search(set(fixed),set(q),191,8000,CUBE)
            if st=='UNKNOWN':continue
            assert st=='FOUND' and len(w)>=192 and not inspect(w) and fixed<=set(w)
            return dict(replaced_index=i,two_chords=chords,parameters=params,fixed=len(fixed),edges=len(w)-1,witness=w)
    raise AssertionError('missing corrupted positive control')

def run():
    print(json.dumps({'control':control()}),flush=True)
    rows=[(i,l.split()[1]) for i,l in enumerate(open(ROOT/'q9_new189_nearmisses.words')) if l.split()[0]=='2']
    assert len(rows)==34
    counts=Counter(); seen=set(); templates=0
    for i,word in rows:
        p=[0]
        for d in word:p.append(p[-1]^(1<<int(d)))
        chords=inspect(p)
        assert len(chords)==2 and len(p)==193
        for fixed,params in regions(p,chords):
            templates+=1
            if fixed in seen: continue
            seen.add(fixed)
            st,w=search(set(fixed),set(p),192,2500,CUBE)
            if w:assert len(w)>=193 and not inspect(w) and fixed<=set(w)
            counts[st]+=1
            print(json.dumps(dict(row=i,chords=chords,params=params,fixed=len(fixed),status=st,witness=w),separators=(',',':')),flush=True)
            if w: return
    print(json.dumps(dict(counts=counts,templates=templates,distinct=len(seen))),flush=True)
if __name__=='__main__': run()
