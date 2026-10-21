"""Round 3 driver: ladders of symmetric-snake SAT instances (sym3.SymModel).

  drive3.py --n 9 --ks 4 3 --edges 180 186 190 192 --tl 600 --log L.jsonl --outdir D

For each class (k, w) with w fixed by the parity of edges+1, run one
instance per edge count and append a JSON record.  SAT snakes are checked
again by sym3.is_snake and saved as {"vertex_sequence": [...]}.  With
--stop-unknown, a ladder stops at the first UNKNOWN or UNSAT.
"""
import argparse
import json
import os
import resource
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sym3 import SymModel, is_snake  # noqa: E402


def disk_ok(path):
    return shutil.disk_usage(path).free > 300 * 2**20


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=9)
    ap.add_argument("--ks", type=int, nargs="+", required=True)
    ap.add_argument("--edges", type=int, nargs="+", required=True)
    ap.add_argument("--tl", type=float, default=300)
    ap.add_argument("--log", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--stop-unknown", action="store_true")
    ap.add_argument("--noq4", action="store_true")
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    for k in a.ks:
        for e in a.edges:
            w = 0 if (e + 1) % 2 else 1
            if 2 * k + w > a.n or (k, w) == (0, 1):
                continue
            if not disk_ok("/"):
                print("low disk, stop", flush=True)
                return
            t0 = time.time()
            M = SymModel(a.n, k, w, e + 1, q4=not a.noq4)
            st, p = M.run(a.tl)
            rec = dict(n=a.n, k=k, w=w, edges=e, status=st, time=round(time.time() - t0, 1),
                       cuts=M.cuts, clauses=M.nclauses,
                       rss_mb=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024)
            if p:
                assert is_snake(p, a.n) and len(p) == e + 1
                fn = os.path.join(a.outdir, f"sym-n{a.n}-k{k}-e{e}.json")
                json.dump({"vertex_sequence": p, "class": [k, w]}, open(fn, "w"))
                rec["file"] = fn
            M.close()
            print(json.dumps(rec), flush=True)
            with open(a.log, "a") as f:
                f.write(json.dumps(rec) + "\n")
            if a.stop_unknown and st != "SAT":
                break


if __name__ == "__main__":
    main()
