"""Summarize the search logs (jsonl) into data/summary.json and re-check stored snakes."""
import collections
import glob
import gzip
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lns import is_snake  # noqa: E402

here = os.path.dirname(os.path.abspath(__file__))
data = os.path.join(here, "../data")


def load(path):
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as f:
        return [json.loads(l) for l in f if l.strip()]


out = {}
for path in sorted(glob.glob(os.path.join(data, "*.jsonl.gz"))):
    L = load(path)
    name = os.path.basename(path).split(".")[0]
    s = {"records": len(L)}
    if name.startswith("sweep"):
        s["results"] = dict(collections.Counter(r["res"] for r in L))
        s["bank_entries"] = len(set(r["bank"] for r in L))
        s["widths"] = sorted(set(r["w"] for r in L))
        s["solver_seconds"] = round(sum(r["sec"] for r in L), 1)
        s["max_free"] = max(r["free"] for r in L)
    elif name.startswith("walk"):
        s["uphill_193"] = dict(collections.Counter(r["res193"] for r in L))
        s["neutral_moves"] = sum(1 for r in L if r.get("res192") == "SAT")
        s["new_classes"] = L[-1]["classes"]
    elif name.startswith("anneal"):
        s["lengths"] = dict(collections.Counter(r["len"] for r in L))
        s["moves"] = dict(collections.Counter(r.get("moved", "none") for r in L))
        b = [r["bank"] for r in L if r["len"] == 191]
        s["visits_191"] = len(b)
        s["distinct_bank_classes_191"] = len(set(x for x in b if x >= 0))
        s["non_bank_191"] = sum(1 for x in b if x < 0)
    elif name.startswith("ils"):
        s["episodes"] = len(L)
        s["low"] = dict(collections.Counter(r["low"] for r in L))
        s["top"] = dict(collections.Counter(r["top"] for r in L))
        s["bank_classes_reached"] = sorted(set(r["bank"] for r in L if "bank" in r))
        s["new_191_classes"] = max([r.get("new191", 0) for r in L] + [0])
        bad = [r for r in L if "path" in r and not is_snake(r["path"])]
        assert not bad
    out[name] = s

checked = {}
for path in sorted(glob.glob(os.path.join(data, "snake*.json")) + glob.glob(os.path.join(data, "new191*.json"))):
    seq = json.load(open(path))["vertex_sequence"]
    checked[os.path.basename(path)] = {"edges": len(seq) - 1, "is_snake": is_snake(seq)}
out["stored_snakes"] = checked
json.dump(out, open(os.path.join(data, "summary.json"), "w"), indent=1, sort_keys=True)
print(json.dumps(out, indent=1, sort_keys=True))
