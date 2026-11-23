"""Replace two neighboring Q6 visits simultaneously, retaining all other blocks."""

import argparse
import json
from pathlib import Path
from search_q9_anchored_sets import search
from search_q9_wynn_plateau import verify


def load(line):
    fields = line.split()
    n = int(fields[0])
    assert len(fields) == 1 + 2 * n
    sites = []
    for j in range(n):
        cell = int(fields[1 + 2 * j])
        mask = int(fields[2 + 2 * j], 16)
        sites.append((cell, {64 * cell + x for x in range(64) if mask >> x & 1}))
    return sites


def run(src, target, budget, width=2, selected=None):
    for row, line in enumerate(src.read_text().splitlines()):
        seq = load(line)
        seed = set.union(*(s for _, s in seq))
        assert len(seed) == 192
        for i in range(len(seq) - width + 1):
            if selected is not None and (row, i) not in selected:
                continue
            window = range(i, i + width)
            cells = {seq[j][0] for j in window}
            fixed = set.union(*(s for j, (_, s) in enumerate(seq) if j not in window))
            allowed = fixed | {v for v in range(512) if v >> 6 in cells}
            bounded, w = search(
                fixed, seed, target, budget, allowed=allowed, at_least=True
            )
            if w:
                assert verify(w) and len(w) >= target + 1
            yield {
                "row": row,
                "visits": list(window),
                "target": target,
                "fixed": len(fixed),
                "status": bounded,
                "witness": w,
            }
            if w and target >= 192:
                return


if __name__ == "__main__":
    import sys

    sel = None
    if len(sys.argv) > 5:
        sel = {
            (d["row"], d["visits"][0])
            for l in Path(sys.argv[5]).read_text().splitlines()
            if (d := json.loads(l))["status"] == "UNKNOWN"
        }
    for d in run(
        Path(sys.argv[1]),
        int(sys.argv[2]),
        int(sys.argv[3]),
        int(sys.argv[4]) if len(sys.argv) > 4 else 2,
        sel,
    ):
        print(json.dumps(d, separators=(",", ":")), flush=True)
        if int(sys.argv[2]) == 191 and d["witness"]:
            break
