"""Search Q9 by applying reversible transformations to one color of a long snake."""
import argparse
import gzip
import itertools
import json
import subprocess
from verify_q9_center_avoidance import forms, verify

FULL = (1 << 256) - 1
HALVES = [sum(1 << v for v in range(256) if not v & (1 << d)) for d in range(8)]
PLANES = [sum(1 << v for v in range(256) if (m & v).bit_count() % 2) for m in range(256)]


def flip(mask, d):
    step = 1 << d
    return ((mask & HALVES[d]) << step) | ((mask >> step) & HALVES[d])


def translate(mask, t):
    for d in range(8):
        if t & (1 << d):
            mask = flip(mask, d)
    return mask


def enough(mask):
    # A compressed opposite-color vertex has nine possible neighbors, including
    # the equal low byte (the Q9 edge flipping the omitted high bit).
    one = mask
    two = three = 0
    for d in range(8):
        b = flip(mask, d)
        three |= two & b
        two |= one & b
        one |= b
    if (one & ~two).bit_count() < 2:
        return False
    usable = one & ~three
    seen, twice = usable, 0
    for d in range(8):
        b = flip(usable, d)
        twice |= seen & b
        seen |= b
    return not (mask & ~twice)


def solve(batch, binary, positive=False):
    lines = []
    for m in batch:
        # Global translation by the omitted coordinate normalizes fixed color to even.
        side = [v + 256 * (v.bit_count() % 2) for v in range(256) if m & (1 << v)]
        lines.append(" ".join(map(str, [len(side), *side])))
    output = subprocess.run([binary, "--sets"], input="\n".join(lines)+"\n",
                            capture_output=True, text=True, check=True).stdout.splitlines()
    assert len(output) == len(batch)
    for mask, line in zip(batch, output):
        if line.startswith("FOUND "):
            p = list(map(int, line.split()[1:]))
            assert len(p) == 2 * mask.bit_count() + 1
            verify(p)
            assert sum(1 << (v & 255) for v in p[1::2]) == mask
            if not positive:
                print(json.dumps({"vertices":p,"edges":len(p)-1}), flush=True)
        elif line not in ("NO","UNKNOWN"):
            raise ValueError(line)
    return sum(x=="UNKNOWN" for x in output), sum(x.startswith("FOUND ") for x in output)


def run(args):
    paths = {}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p = list(map(int,line.split()))
        if len(p) == 192:
            verify(p)
            paths.setdefault(forms(p,191)[0],p)
    p = next(iter(paths.values()))[:-1]
    ctrl = sum(1 << (v & 255) for v in p[1::2])
    assert enough(ctrl) and solve([ctrl],args.binary,positive=True)==(0,1)
    total = viable = unknown = found = sides = 0
    checked=set()
    for p in list(paths.values())[args.start:args.stop]:
        for offset in (0,1):
            sides += 1
            a=sum(1 << (v & 255) for v in p[offset::2])
            batch=set()
            for t in range(1,256):
                diff=a ^ translate(a,t)
                if args.family=="linear":
                    regions=(PLANES[m] for m in range(1,256) if not (t&m).bit_count()%2)
                else:
                    # Every selected subcube is invariant under translation by t.
                    free=[d for d in range(8) if not (t>>d)&1]
                    regions=(r for ds in itertools.combinations(free,args.width)
                             for r in boxes[ds])
                for region in regions:
                    candidate=a ^ (region & diff)
                    total+=1
                    if candidate not in batch:
                        batch.add(candidate)
            valid=[m for m in batch if enough(m) and m not in checked]
            if valid:
                u,f=solve(valid,args.binary)
                unknown+=u;found+=f;viable+=len(valid);checked.update(valid)
            if found:break
        if found:break
    print(json.dumps(dict(family=args.family,width=args.width,bank=len(paths),start=args.start,
        stop=args.stop,sides=sides,transformations=total,distinct_passing_filter=viable,
        unresolved=unknown,found=found)),flush=True)


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("binary")
    ap.add_argument("family",choices=["linear","boxes"])
    ap.add_argument("start",type=int);ap.add_argument("stop",type=int)
    ap.add_argument("--width",type=int,default=2)
    args=ap.parse_args()
    boxes={}
    for ds in itertools.combinations(range(8),args.width):
        regions=[FULL]
        for d in ds:
            regions=[r & h for r in regions for h in (HALVES[d],FULL^HALVES[d])]
        boxes[ds]=regions
    run(args)
