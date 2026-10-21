"""Rebuild data/round3-summary.json from the round-3 logs (data/r3-*.jsonl.gz)."""
import glob
import gzip
import json
import os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "../data")
out = {}
for fn in sorted(glob.glob(os.path.join(DATA, "r3-*.jsonl.gz"))):
    name = os.path.basename(fn)[3:-9]
    rows = [json.loads(l) for l in gzip.open(fn, "rt")]
    if not rows:
        continue
    if "status" in rows[0] and "step" not in rows[0]:      # drive3 ladders
        out[name] = [{k: r[k] for k in ("n", "k", "w", "edges", "status", "time")} for r in rows]
    elif rows[0].get("mode") == "grow":                     # drive2 grow
        out[name] = dict(steps=len(rows), start=rows[0]["L"], best=max(r["len"] for r in rows),
                         up=Counter(r["up"] for r in rows))
    else:                                                   # symlns
        best = max(r.get("new_len", r["len"]) for r in rows)
        out[name] = dict(k=rows[0]["k"], w=rows[0]["w"], steps=len(rows), start=rows[0]["len"],
                         best=best, first_best_step=min(r["step"] for r in rows if r.get("new_len") == best),
                         moves=Counter(r["move"] + ":" + r["status"] for r in rows))
json.dump(out, open(os.path.join(DATA, "round3-summary.json"), "w"), indent=1, sort_keys=True)
print(json.dumps(out, indent=1, sort_keys=True)[:3000])
