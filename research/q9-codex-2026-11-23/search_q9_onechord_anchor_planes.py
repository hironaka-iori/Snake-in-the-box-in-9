"""Release one side of an affine parity plane through a single chord, allowing insertions everywhere."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
from search_q9_onechord_joint import pair
from search_q9_parent_junctions import check
from search_q9_anchored_sets import search

def templates(path,i,j,rng):
    # A separating functional frees precisely one end of the offending chord.
    masks=[m for m in range(1,512) if (path[i]^path[j])&m and 2<=m.bit_count()<=6]
    rng.shuffle(masks)
    for index in range(4):
        mask=masks[index]
        side=(path[i if index%2 else j]&mask).bit_count()%2
        fixed={v for v in path if (v&mask).bit_count()%2==side}
        yield mask,side,fixed

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("file",type=Path)
    ap.add_argument("--stride",type=int,default=4)
    ap.add_argument("--offset",type=int,default=0)
    ap.add_argument("--budget",type=int,default=5000)
    args=ap.parse_args()
    for idx,s in enumerate(args.file.read_text().splitlines()):
        if idx%args.stride!=args.offset:continue
        p=list(map(int,s.split()))
        i,j=pair(p)
        rng=random.Random(1009*idx+517)
        for mask,side,fixed in templates(p,i,j,rng):
            status,w=search(fixed,set(p),192,args.budget,at_least=True)
            if w:
                check(w,192)
                assert fixed<=set(w)
            print(json.dumps(dict(row=idx,mask=mask,side=side,anchors=len(fixed),status=status,witness=w)),flush=True)
            if w:return
if __name__=="__main__":main()
