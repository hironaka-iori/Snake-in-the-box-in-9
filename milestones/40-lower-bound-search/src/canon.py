#!/usr/bin/env python3
"""Collect snakes from search logs, validate them independently, canonicalise
under the hyperoctahedral group of Q9 and count inequivalent classes.
Canonical form of a path: transition sequence with coordinates relabelled in
order of first use, minimised over the two directions (translation is
absorbed by the transition sequence)."""
import sys, glob, json
from check import check  # noqa
def canon(seq):
    best = None
    for s in (seq, seq[::-1]):
        tr = [(s[i] ^ s[i+1]).bit_length() - 1 for i in range(len(s)-1)]
        lab = {}; out = []
        for t in tr:
            if t not in lab: lab[t] = len(lab)
            out.append(lab[t])
        out = tuple(out)
        if best is None or out < best: best = out
    return best
if __name__ == "__main__":
    minedges = int(sys.argv[1]); files = sys.argv[2:]
    classes = {}
    for f in files:
        for line in open(f):
            if not line.startswith("BEST"): continue
            seq = [int(t) for t in line.split(":", 1)[1].split()]
            if len(seq) - 1 < minedges: continue
            err = check(9, seq)
            if err: print("INVALID", f, err); continue
            c = canon(seq)
            classes.setdefault(c, []).append((f, seq))
    by = {}
    for c, v in classes.items(): by.setdefault(len(c), []).append(c)
    for L in sorted(by, reverse=True): print(f"edges={L}: {len(by[L])} classes, {sum(len(classes[c]) for c in by[L])} hits")
    import os
    bank = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../work/bank9.json")))
    bankc = {canon(e["vertex_sequence"]) for e in bank}
    n191 = [c for c in classes if len(c) == 191]
    print(f"191-edge classes in bank: {sum(c in bankc for c in n191)} of {len(n191)}")
    json.dump([{"edges": len(c), "in_bank": c in bankc, "hits": len(v), "vertex_sequence": v[0][1]}
               for c, v in sorted(classes.items(), key=lambda kv: -len(kv[0]))], open("classes.json", "w"))
