"""Enumerate all 191-edge snakes whose unweighted projection agrees with a stored snake."""
import argparse
from collections import Counter
import json
from pathlib import Path
from bank_pivots import canonical_word
from fibre_laplacian import decide
from punctured_lift import project
from punctured_pit import examine,groups
from solve import BANK,BANK_HASH,sha256,save,defects


def classify(index,W,sources,bank,classes,budget):
    occupied=set(W);k=192-len(W)
    possible={v for v in W if sum((v^(1<<j)) in occupied for j in range(8))<=2}
    known={}
    for source,axis in sources:
        P,sw=project(bank[source]["vertex_sequence"],axis)
        assert set(P)==occupied
        R=frozenset(P[j] for j in sw)
        known.setdefault(R,set()).add(source)
    found=[];used=set(known);conflicts=cuts=0
    for R,origins in known.items():
        assert len(R)==k and R<=possible
        # The independent algebraic reconstruction also checks that the stored
        # representatives are all the lifts for this labelled doubled set.
        r=decide(W,R,8,count_all=True,collect_paths=True)
        assert r["solutions"]==1
        assert set(classes[canonical_word(q)] for q in r["paths"])==origins
    if possible==set(next(iter(known))) and len(possible)==k:
        status="forced"
    else:
        while True:
            r=examine(W,str(index),budget,desired=192,forbidden_doubles=used)
            conflicts+=r["stats"]["conflicts"];cuts+=len(r["dynamic"])
            if r["status"]!="FOUND":
                status=r["status"];break
            q=r["witness"];assert not defects(q)
            counts=Counter(v&255 for v in q)
            R=frozenset(v for v,n in counts.items() if n==2)
            assert set(counts)==occupied and R not in used and len(R)==k
            used.add(R)
            z=decide(W,R,8,count_all=True,collect_paths=True)
            words=[canonical_word(p) for p in z["paths"]];assert canonical_word(q) in words
            found.append(dict(doubled=sorted(R),paths=z["paths"],bank_classes=[classes.get(w) for w in words]))
    return dict(index=index,sources=sources,status=status,known=len(known),other=found,
                required=k,possible=len(possible),conflicts=conflicts,cycle_cuts=cuts)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=150000);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw);classes={canonical_word(z["vertex_sequence"]):i for i,z in enumerate(bank)}
    assert len(classes)==len(bank);groups_by_shape=groups()
    rows=[];file=Path(f"unweighted-fibres-{a.first}-{a.stop}-{a.budget}.json")
    for i in range(a.first,min(a.stop,len(groups_by_shape))):
        W,sources=groups_by_shape[i];rows.append(classify(i,W,sources,bank,classes,a.budget))
        if len(rows)%10==0:save(file,rows)
    save(file,rows);print(len(rows),Counter(r["status"] for r in rows),sum(len(r["other"]) for r in rows),flush=True)
