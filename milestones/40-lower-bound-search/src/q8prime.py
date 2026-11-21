#!/usr/bin/env python3
"""Make a Q9 start set from two long Q8 snakes glued across the facet x8.
usage: q8prime.py SEED OUTFILE  (run from milestones/40-lower-bound-search)
Runs bin/surgery -n 8 twice (30 s each) for Q8 snakes P, R, then writes
P (facet x8=0) followed by phi(R) in facet x8=1, with phi a random signed
coordinate permutation of Q8.
bin/surgery -init adds the listed vertices greedily while the set stays a
snakepit, so incompatible vertices are dropped."""
import random, subprocess, sys
from check import check

def q8snake(seed):
    out = f"/tmp/q8prime_{seed}.txt"
    subprocess.run(["bin/surgery", "-n", "8", "-s", str(seed), "-steps", "100000000000", "-t", "30",
                    "-r", "90", "-b", "4", "-T0", "0.65", "-T1", "0.65", "-o", out], check=True,
                   stdout=subprocess.DEVNULL)
    best = None
    for line in open(out):
        if line.startswith("BEST"):
            s = [int(t) for t in line.split(":", 1)[1].split()]
            if check(8, s) is None and (best is None or len(s) > len(best)):
                best = s
    return best

def main():
    seed = int(sys.argv[1]); rng = random.Random(seed)
    P = q8snake(seed * 2 + 1); R = q8snake(seed * 2 + 2)
    perm = list(range(8)); rng.shuffle(perm); flip = rng.randrange(256)
    def phi(v):
        y = 0
        for i in range(8):
            if v >> i & 1: y |= 1 << perm[i]
        return y ^ flip
    R2 = [phi(v) | 256 for v in R]
    if rng.random() < 0.5: R2 = R2[::-1]
    with open(sys.argv[2], "w") as f:
        f.write(" ".join(map(str, P + R2)) + "\n")
    print(f"q8 snakes {len(P)-1} and {len(R)-1} edges")

if __name__ == "__main__":
    main()
