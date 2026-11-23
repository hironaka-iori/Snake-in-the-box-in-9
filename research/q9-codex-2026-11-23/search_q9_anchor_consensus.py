"""Align near-snakes by their common obstruction and release it during recombination."""
import argparse
import json
import random
from itertools import combinations, permutations
from pathlib import Path
from match_q9_anchor_obstruction import longest_component,labels
from search_q9_break_matched_anchors import cases,search,check

def aligned(path, source, target):
    shape=longest_component(source)
    src=labels(shape)
    dest=longest_component(target)
    assert len(dest)==len(shape)
    output=set()
    for line in (dest,dest[::-1]):
        flip=labels(line)
        common=dict(zip(src,flip))
        if len(set(common.values()))!=len(common) or any(common[a]!=b for a,b in zip(src,flip)):continue
        rest=sorted(set(range(9))-common.keys())
        for order in permutations(set(range(9))-set(common.values())):
            perm=common|dict(zip(rest,order))
            lut=[line[0]^sum(1<<b for a,b in perm.items() if (v^shape[0])&(1<<a)) for v in range(512)]
            if {lut[v] for v in source}==target:
                output.add(tuple(lut[v] for v in path))
    if not output:raise ValueError("obstruction alignment failed")
    return sorted(output)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--target",type=int,default=192)
    parser.add_argument("--budget",type=int,default=5000)
    parser.add_argument("--limit",type=int,default=3000)
    opt=parser.parse_args()
    target=set(json.loads(Path("q9_onechord_62anchors.json").read_text())["anchors"])
    parents=[]
    for name,row,p,i,j,image in cases():
        for seq in aligned(p,set(image),target):
            parents.append((name,row,set(seq),{seq[i],seq[j]}))
    rng=random.Random(712613)
    pairs=list(combinations(range(len(parents)),2))
    rng.shuffle(pairs)
    seen=set()
    for ai,bi in pairs:
        a,b=parents[ai],parents[bi]
        if a[:2]==b[:2]:continue
        shared=a[2]&b[2];conflict=a[3]|b[3]
        outside=shared-target-conflict
        if not outside:continue
        for radius in (1,2):
            # Free all 62 anchors as well as shared vertices near the chord.
            fixed={v for v in outside if min((v^w).bit_count() for w in conflict)>radius}
            if not fixed:continue
            for mode in ("whole","union"):
                domain=(set(range(512)) if mode=="whole" else a[2]|b[2])
                # Partition sampled escapes by choosing an actual anchor to remove.
                missing=rng.choice(sorted(target))
                domain=domain-{missing}
                key=(frozenset(fixed),frozenset(domain))
                if key in seen:continue
                seen.add(key)
                s,w=search(fixed,a[2],opt.target,opt.budget,allowed=domain,at_least=True)
                if w:
                    check(w,opt.target)
                    assert fixed<=set(w)<=domain
                print(json.dumps(dict(parent_a=a[:2],parent_b=b[:2],radius=radius,mode=mode,
                    missing=missing,fixed=len(fixed),domain=len(domain),status=s,witness=w)),flush=True)
                if (w and len(w)>=193) or len(seen)>=opt.limit:return
if __name__=="__main__":main()
