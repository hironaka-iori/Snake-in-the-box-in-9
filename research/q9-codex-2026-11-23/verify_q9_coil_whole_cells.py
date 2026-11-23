"""Audit axis-domain coverage, positive paths and equivalent decisions on the coil."""
import sys
import json
from itertools import combinations
from collections import Counter
from pathlib import Path
from verify_q9_six_cube_coverage import pairwise


def automorphisms(cycle):
    n=len(cycle)
    steps=[(a^b).bit_length()-1 for a,b in zip(cycle,cycle[1:]+cycle[:1])]
    for anchor in range(n):
        for sign in (1,-1):
            ordered=[cycle[(anchor+sign*j)%n] for j in range(n)]
            image=[(a^b).bit_length()-1 for a,b in zip(ordered,ordered[1:]+ordered[:1])]
            perm=dict(zip(steps,image))
            if len(perm)!=9 or len(set(perm.values()))!=9 or any(perm[a]!=b for a,b in zip(steps,image)):continue
            def transform(v):
                return ordered[0] ^ sum(((v^cycle[0])>>i&1)<<j for i,j in perm.items())
            assert all(transform(x)==y for x,y in zip(cycle,ordered))
            yield perm,transform(0)


def image_key(key,perm,shift):
    axes,labels=key
    new=tuple(sorted(perm[a] for a in axes))
    labels=tuple(sorted(sum((((v>>i&1) ^ (shift>>perm[a]&1))<<new.index(perm[a])) for i,a in enumerate(axes)) for v in labels))
    return new,labels


def load(fname):
    return [json.loads(s) for s in Path(fname).read_text().splitlines()]


if __name__=='__main__':
    cycle=json.loads(Path('q9_coil_open_191_witness.json').read_text())['cycle']
    assert len(cycle)==len(set(cycle))==192
    assert all(((x^cycle[j]).bit_count()==1) == (j-i in (1,191)) for i,x in enumerate(cycle) for j in range(i+1,len(cycle)))
    group=list(automorphisms(cycle))
    known={}
    for name in sys.argv[1:] or ['q9_coil_whole_cells_triple_192.jsonl']:
        for r in load(name):
            key=tuple(r['axes']),tuple(r['cells'])
            assert r['target']==192
            if r['witness']:pairwise(r['witness'],len(r['witness'])-1);assert len(r['witness'])>=193
            if key in known:
                assert known[key]=='UNKNOWN' or r['status'] in ('UNKNOWN',known[key])
            if r['status']!='UNKNOWN' or key not in known:known[key]=r['status']
    original=Counter(known.values())
    for key,st in list(known.items()):
        if st=='UNKNOWN':continue
        for perm,shift in group:
            target=image_key(key,perm,shift)
            assert target not in known or known[target] in ('UNKNOWN',st)
            known[target]=st
    total=sum(1 for _ in combinations(range(9),3))*sum(1 for _ in combinations(range(8),3))
    positive=load('q9_coil_whole_cells_191_control.jsonl')[0]
    pairwise(positive['witness'],191)
    print(json.dumps(dict(positive_edges=191,symmetries=len(group),shortlist=total,raw=original,using_symmetry=Counter(known.values()))))
