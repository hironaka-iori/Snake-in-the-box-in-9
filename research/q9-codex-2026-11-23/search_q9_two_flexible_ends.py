"""Split open one-end cases by endpoint, or add a free visit at both ends."""
import argparse
import json
import random
from pathlib import Path

from search_q9_flexible_corners import solve
from search_q9_square_fiber_lift import check, projections


def verify(w, target):
    pos = {v: i for i, v in enumerate(w)}
    assert len(pos) == len(w) >= target + 1
    assert all(0 <= v < 512 for v in w)
    for i, v in enumerate(w):
        actual = {pos[v^(1<<d)] for d in range(9) if v^(1<<d) in pos}
        expected = {j for j in (i-1,i+1) if 0 <= j < len(w)}
        assert actual == expected


def split_cases():
    data = json.loads(Path("q9_flexible_frontier.json").read_text())
    for key, first in data["unresolved"]["q9_flexible_endpoint_relative_192.jsonl"]:
        q = bytes.fromhex(key)
        assert (len(q)-1)%2 == first
        ids = list(range(first,len(q)-1,2))
        for k in range(7):
            p = q[:-1] + bytes([q[-2] ^ (1<<k)])
            yield [key, first, k], p, ids, []


def two_ends(path, limit, control):
    bank = {}
    for line in Path(path).read_text().splitlines():
        w = list(map(int, line.split()))
        verify(w,191)
        steps = [(x^y).bit_length()-1 for x,y in zip(w,w[1:])]
        for p, h in projections(steps):
            bank.setdefault(bytes(p), h)
    keys = sorted(bank)
    rng = random.Random(2011192)
    rng.shuffle(keys)
    for i, p in enumerate(keys[:limit]):
        h = bank[p]
        if control:
            q = p
            hints = h
        else:
            q = bytes([p[0]^1])+p+bytes([p[-1]^1])
            hints = [[h[0][0]],*h,[h[-1][-1]]]
        ids = [0, *range(2+(i%2),len(q)-2,2), len(q)-1]
        assert min(b-a for a,b in zip(ids,ids[1:])) >= 2
        yield [p.hex(),i%2],q,ids,hints


if __name__ == "__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("mode",choices=["split","both","control"])
    ap.add_argument("--bank",default="/tmp/q9_core_191bank_m19.txt")
    ap.add_argument("--limit",type=int,default=1600)
    ap.add_argument("--cap",type=int,default=3000)
    args=ap.parse_args()
    target=191 if args.mode=="control" else 192
    cases=split_cases() if args.mode=="split" else two_ends(args.bank,args.limit,args.mode=="control")
    for key,q,ids,hints in cases:
        s,w=solve(q,hints,ids,target,args.cap,True)
        if w:verify(w,target)
        print(json.dumps([s,key,w],separators=(",",":")),flush=True)
        if w:break
