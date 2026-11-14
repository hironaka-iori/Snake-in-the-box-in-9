"""Allow every cube-neighbour parity check inside an arbitrary coordinate subcube to change."""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path


def patterns(d):
    if d==4:
        # This output is complementary to the exhaustive radius-three survey.
        bounds=range(4,9)
    else:bounds=range(4,5)
    seen=set()
    for axes in combinations(range(9),d):
        mask=sum(1<<b for b in axes)
        offsets=[v for v in range(512) if v&~mask==0 and v.bit_count()%2==0]
        for base in range(512):
            if base&mask:continue
            shift=base if base.bit_count()%2==0 else base^(1<<axes[0])
            face=[v^shift for v in offsets]
            for k in bounds:
                for changes in combinations(face,k):seen.add(tuple(sorted(changes)))
    return sorted(seen)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("dimension",type=int,choices=(3,4))
    p.add_argument("--export",type=Path);args=p.parse_args()
    pats=patterns(args.dimension)
    print(len(pats),Counter(map(len,pats)),flush=True)
    if args.export:
        with args.export.open("w") as f:
            for pattern in pats:f.write(" ".join(map(str,[len(pattern),*pattern]))+"\n")
