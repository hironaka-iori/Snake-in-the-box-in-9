"""Reconstruct saved weights from literal rule tables; no builder or solver import.

Checks full (direction, history, six-code) keys, endpoints, and all saved weights.
This finite-array check does not establish completeness of a defined proof graph.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "work/solver_packages"))
import numpy as np

def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def canon(word):
    names = {}
    out = []
    for letter in word:
        if letter not in names:
            names[letter] = len(names)
        out.append(names[letter])
    return tuple(out)

def encode(symbols):
    result = 0
    for symbol in symbols:
        result = 6 * result + symbol - 1
    return result

def main():
    start = time.monotonic()
    old = ROOT / "milestones/72-four-count-proof-closure/critical-current"
    geo_path = ROOT / "milestones/59-extended-share-window/data/geometry.json"
    model_path = ROOT / "milestones/59-extended-share-window/extended/data/model.json"
    hist_path = ROOT / "milestones/67-critical-family-charge/data/full-model.json"
    completed_path = ROOT / "milestones/73-countfree-share-catalogue/data/proved-model.json"
    floor18_path = ROOT / "milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json"
    files = [geo_path, model_path, hist_path, completed_path, floor18_path,
             old / "build/source-graph.npz", old / "data/source-proved-model.json",
             old / "build/countfree16-all-except012034x20-except012310x12-graph.npz",
             ROOT / "milestones/70-proof-supported-share-model/scripts/build.py",
             old / "scripts/prepare.py",
             ROOT / "milestones/73-countfree-share-catalogue/scripts/evaluate_checked.py",
             ROOT / "milestones/92-full-witness-batch/lean/DefinedProofGraph.lean",
             ROOT / "milestones/93-defined-graph-potential/audit/weight-bridge-plan.md"]
    pins = {str(p.relative_to(ROOT)).replace("\\", "/"): sha(p.read_bytes()) for p in files}
    meta, model, hist = read(old / "data/source-proved-model.json"), read(model_path), read(hist_path)
    geometry = read(geo_path)["patterns"]
    completed_meta, floor18_meta = read(completed_path), read(floor18_path)
    with np.load(old / "build/source-graph.npz") as z:
        source = {k: z[k] for k in z.files}
    hashes = {k: sha(v.tobytes()) for k, v in source.items()}
    assert hashes == meta["arrays_sha256"] == completed_meta["source_arrays_sha256"]
    n = len(source["U"])
    assert n == 4947008 and meta["states"] == 1601856
    d, q, c = (source[k].astype(np.int64) for k in ("direction", "history", "count_code"))
    assert np.all((0 <= d) & (d < 505) & (0 <= q) & (q < 75) & (0 <= c) & (c < 46656))
    keys = (75 * d + q) * 46656 + c
    assert np.all(keys[1:] > keys[:-1]), "Full keys must be distinct and lexicographically ordered."
    symbols = np.stack([c // 6**j % 6 + 1 for j in range(5, -1, -1)], axis=1)
    entering = 120 * symbols[:, 5]
    extensions = model["extensions"]
    assert len(extensions) == len(geometry) == 505
    assert all(ds == item["directions"] for ds, item in zip(extensions, geometry))
    suffix = [canon(ds[-6:]) for ds in extensions]
    unoriented = [min(suffix[i], canon(ds[-6:][::-1])) for i, ds in enumerate(extensions)]
    shape_text = ["".join(map(str, word)) for word in unoriented]
    geometric = np.array([g["share_lower"] for g in geometry], dtype=np.int64)[d]
    conditioned = np.zeros(n, dtype=np.int64)
    forward = [((0,1,2,3,1,4),(3,3,3,6,5),48),
               ((0,1,2,3,4,5),(3,6,2,3,6),96),
               ((0,1,2,0,3,4),(6,3,6,3,3),96),
               ((0,1,2,3,4,5),(4,6,2,3,6),96)]
    rules = forward + [(canon(w[::-1]), counts[::-1], lower) for w, counts, lower in forward]
    rule_counts = []
    for word, counts, lower in rules:
        direction_hit = np.array([s == word for s in suffix], dtype=bool)
        hit = direction_hit[d] & (c % 7776 == encode(counts))
        conditioned[hit] = np.maximum(conditioned[hit], lower)
        rule_counts.append(dict(word=list(word), symbols=list(counts), lower=lower,
                                matching_saved_edges=int(hit.sum())))
    history_credit = np.zeros(n, dtype=np.int64)
    prefixes = [tuple(p) for p in hist["prefixes"]]
    shapes = {tuple(s): i for i, s in enumerate(model["direction_shapes"])}
    assert len(prefixes) == 75 and len(shapes) == 132 and model["states"] == 1026432
    assert Counter(p["mode"] for p in hist["patterns"]) == {"share": 55, "exclusion": 3}
    blocks = 75 * d + q
    cuts = np.r_[0, np.flatnonzero(blocks[1:] != blocks[:-1]) + 1, n]
    history_hits = Counter()
    cap_hits = Counter()
    emitted_exclusions = 0
    for lo, hi in zip(cuts[:-1], cuts[1:]):
        di, qi = int(d[lo]), int(q[lo])
        ds = extensions[di]
        ps, ts = shapes[canon(ds[:8])], shapes[canon(ds[1:])]
        assert qi == 0 or hist["compatible_shapes"][qi] == ps
        emitted = prefixes[qi] + (di,)
        matches = [j for j, p in enumerate(prefixes) if p and len(p) <= len(emitted) and emitted[-len(p):] == p]
        nq = max(matches, key=lambda j: len(prefixes[j])) if matches else 0
        assert nq == 0 or hist["compatible_shapes"][nq] == ts
        u = (ps * 7776 if qi == 0 else 1026432 + (qi - 1) * 7776) + c[lo:hi] // 6
        v = (ts * 7776 if nq == 0 else 1026432 + (nq - 1) * 7776) + c[lo:hi] % 7776
        assert np.array_equal(u, source["U"][lo:hi]), (di, qi, "source")
        assert np.array_equal(v, source["V"][lo:hi]), (di, qi, "target")
        for index, p in enumerate(hist["patterns"]):
            if len(emitted) < 3 or emitted[-3:] != tuple(p["signature"]):
                continue
            hit = np.ones(hi - lo, dtype=bool)
            for index_s, cap in p["caps"].items():
                hit &= symbols[lo:hi, int(index_s)] <= cap
            if p["mode"] == "exclusion":
                emitted_exclusions += 1
                assert not hit.any(), (di, qi, "retained excluded key")
            else:
                row = history_credit[lo:hi]
                np.maximum(row, p["geometric_lower"], out=row)
                row[hit] = np.maximum(row[hit], p["lower"])
                history_hits[index] += int(hi - lo)
                cap_hits[index] += int(hit.sum())
    assert len(cuts) - 1 == 791
    distinct = np.array([len(set(ds[-6:])) == 6 for ds in extensions], dtype=bool)[d]
    share120_hit = distinct & ((c % 7776 == encode((4,5,4,2,6))) | (c % 7776 == encode((6,2,4,5,4))))
    share120 = 120 * share120_hit.astype(np.int64)
    base_credit = np.maximum.reduce([geometric, conditioned, history_credit, share120])
    base_weight = entering + base_credit
    assert np.array_equal(base_weight, source["weight"]), "Independent base-weight mismatch."
    completed = {"012031":16,"012032":0,"012034":0,"012301":0,"012304":16,
                 "012310":12,"012314":16,"012340":0,"012345":12}
    reduced = {"012031":16,"012032":16,"012034":18,"012301":16,"012304":16,
               "012310":12,"012314":16,"012340":16,"012345":16}
    assert {"".join(map(str, row["shape"])):row["share"] for row in completed_meta["countfree_floors"]} == {s:v for s,v in completed.items() if v}
    assert set(shape_text) == set(completed) == set(reduced)
    profiles = {}
    for name, floors, expected in [("completed", completed, completed_meta["weight_sha256"]),
                                    ("conditional_floor18", reduced, floor18_meta["weight_sha256"])]:
        floor = np.array([floors[s] for s in shape_text], dtype=np.int64)[d]
        weight = entering + np.maximum(base_credit, floor)
        reference = np.maximum(source["weight"].astype(np.int64), entering + floor)
        assert np.array_equal(weight, reference)
        digest = sha(weight.astype("<i8", copy=False).tobytes())
        assert digest == expected, name
        profiles[name] = dict(floors=floors, edges_compared=n, mismatches=0, weight_i64_sha256=digest,
                              improved_edges_from_source=int((weight > source["weight"]).sum()),
                              minimum=int(weight.min()), maximum=int(weight.max()))
    full = dict(reduced, **{"012034":20})
    full_floor = np.array([full[s] for s in shape_text], dtype=np.int64)[d]
    full_weight = entering + np.maximum(base_credit, full_floor)
    with np.load(old / "build/countfree16-all-except012034x20-except012310x12-graph.npz") as z:
        assert set(z.files) == set(source)
        for name in z.files:
            expected = full_weight if name == "weight" else source[name]
            assert np.array_equal(z[name], expected), ("full20", name)
    elapsed = time.monotonic() - start
    assert elapsed < 300, elapsed
    output = dict(status="PASS_INDEPENDENT_SAVED_KEY_WEIGHT_RECONSTRUCTION", edges=n, contexts=791,
                  raw_states=1601856, source_files_sha256=pins, source_arrays_sha256=hashes,
                  full_keys_strictly_increasing=True, endpoint_mismatches=0, source_weight_mismatches=0,
                  source_weight_i64_sha256=sha(base_weight.astype("<i8", copy=False).tobytes()),
                  profiles=profiles, full20_saved_graph_all_columns_match=True,
                  count_conditioned_rules=rule_counts, share120_matching_saved_edges=int(share120_hit.sum()),
                  history_share_rules_with_saved_emission=len(history_hits),
                  history_share_emitted_edges={str(k):v for k,v in sorted(history_hits.items())},
                  history_capped_edges={str(k):v for k,v in sorted(cap_hits.items())},
                  exclusion_rule_context_matches=emitted_exclusions,
                  component_i64_sha256={k:sha(v.astype("<i8", copy=False).tobytes()) for k,v in
                      [("geometry",geometric),("count_conditioned",conditioned),("history",history_credit),("share120",share120)]},
                  numerical_seconds=elapsed, script_sha256=sha(Path(__file__).read_bytes()),
                  scope="All saved full keys only. No accepted-diagram extras enumerated, no new Lean theorem, solver run, local refutation, potential check or global snake bound.")
    (HERE / "data/weight-model-audit.json").write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k:output[k] for k in ["status","edges","contexts","endpoint_mismatches","source_weight_mismatches","profiles","numerical_seconds"]}, indent=2))

if __name__ == "__main__":
    main()
