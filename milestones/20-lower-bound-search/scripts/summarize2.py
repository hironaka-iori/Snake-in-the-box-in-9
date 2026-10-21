"""Rebuild data/round2-summary.json from the round-2 logs (data/r2-*.jsonl.gz)."""
import collections
import glob
import gzip
import json
import os

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../data")
out = {}
for f in sorted(glob.glob(os.path.join(D, "r2-*.jsonl.gz"))):
    rows = [json.loads(l) for l in gzip.open(f, "rt")]
    name = os.path.basename(f)[3:-9]
    s = {"instances": len(rows)}
    key = "res" if rows and "res" in rows[0] else "up"
    s["results"] = dict(collections.Counter(r.get(key) for r in rows))
    s["found"] = sum(1 for r in rows if "FOUND" in r)
    fr = [r["free"] for r in rows if r.get(key) == "UNSAT" and "free" in r]
    if fr:
        s["max_free_unsat"] = max(fr)
    fu = [r["free"] for r in rows if r.get(key) == "UNKNOWN" and "free" in r]
    if fu:
        s["min_free_unknown"] = min(fu)
    if "bank" in rows[0]:
        s["bank_entries"] = len({r["bank"] for r in rows})
    if name == "endsadapt":
        best = {}
        for r in rows:
            if r["res"] == "UNSAT":
                best[r["bank"]] = max(best.get(r["bank"], 0), r["a"] + r["b"])
        s["largest_unsat_release_per_entry"] = dict(sorted(collections.Counter(best.values()).items()))
        s["entries_without_unsat"] = len({r["bank"] for r in rows}) - len(best)
    if name.startswith("grow"):
        s["max_edges"] = max(r["len"] for r in rows)
        s["bank_classes_at_191"] = sorted({r["bank"] for r in rows if "bank" in r})
    if name.startswith("face"):
        s["distinct_faces"] = len({(r["bank"], tuple(r["dims"]), r["base"]) for r in rows})
    out[name] = s
json.dump(out, open(os.path.join(D, "round2-summary.json"), "w"), indent=1)
print(json.dumps(out, indent=1))
