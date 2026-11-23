"""Look for a 191-step snake outside the public bank and immediately test both ends."""
from itertools import combinations,permutations
from pathlib import Path
from collections import defaultdict
from repair_q9_time_projection import repair, valid
import argparse, json, random


def split(word, mask):
    visible,hidden={},{}
    proj=[]
    flips=[]
    for step in word:
        if step&mask:
            proj.append(0)
            flips.append(hidden.setdefault(step,len(hidden)))
        else:
            proj.append(visible.setdefault(step,1+len(visible)))
    return bytes(proj),bytes(flips)


def permutations_of_labels(flips,d):
    assert flips and flips[0]==0
    for tail in permutations(range(1,d),max(flips)):
        perm=(0,)+tail
        v=0
        labels=[v]
        for j in flips:
            v^=1<<perm[j]
            labels.append(v)
        yield bytes(labels)


def load(path):
    return [list(map(int,l.split())) for l in Path(path).read_text().splitlines() if l.strip()]


def words(p):
    return [a^b for a,b in zip(p,p[1:])]


def canonical(p):
    seq=words(p)
    return min(split(seq,0)[0],split(reversed(seq),0)[0])


def extensions(p):
    for q in (p,p[::-1]):
        for d in range(9):
            extended=q+[q[-1]^(1<<d)]
            if valid(extended):
                yield extended


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('bank');ap.add_argument('seeds')
    ap.add_argument('d',type=int);ap.add_argument('count',type=int)
    ap.add_argument('budget',type=int);ap.add_argument('--seed',type=int,default=1001)
    ap.add_argument('--control',action='store_true')
    a=ap.parse_args()
    bank=list({canonical(p):p for p in load(a.bank)}.values())
    assert len(bank)==len({canonical(p) for p in bank})==131
    assert all(len(p)==192 and valid(p) for p in bank)
    target=bank.pop(0) if a.control else None
    classes={canonical(p) for p in bank}
    axes=list(combinations(range(9),a.d))
    masks=[sum(1<<i for i in row) for row in axes]
    old=defaultdict(set)
    for p in bank:
        w=words(p)
        for seq in (w,w[::-1]):
            for mask in masks:
                visible,hidden=split(seq,mask)
                old[visible].add(hidden)
    seeds=[target] if a.control else [arm for p in load(a.seeds) for arm in [p[:-1],p[1:]]]+bank
    todo=list(range(len(seeds)*len(axes)))
    random.Random(a.seed).shuffle(todo)
    seen=set()
    for task in todo:
        i,j=divmod(task,len(axes))
        p=seeds[i]; w=words(p); key,raw=split(w,masks[j])
        key_rev=split(reversed(w),masks[j])[0]
        canonical_key=min(key,key_rev)
        if canonical_key in seen:continue
        seen.add(canonical_key)
        banned={label for flips in old.get(key,()) for label in permutations_of_labels(flips,a.d)}
        status,path=repair(p,axes[j],a.budget,banned)
        ext=None
        if path is not None:
            assert len(path)==192 and valid(path) and canonical(path) not in classes
            ext=next(extensions(path),None)
        print(json.dumps([status,i,axes[j],len(banned),path,ext],separators=(',',':')),flush=True)
        if ext or path is not None or len(seen)>=a.count:break


if __name__=='__main__':
    main()
