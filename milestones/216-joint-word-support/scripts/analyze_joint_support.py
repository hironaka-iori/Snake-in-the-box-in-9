"""Bounded branch-free comparison on the immutable round215 case22 snapshot."""
import hashlib
import json
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT.parent / "215-word-partner-capacity" / "data" / "case-22"
FILES = {k: CASE / v for k, v in {
    "model": "model.json", "state": "state.json", "families": "support-constraints.json"}.items()}
raw = {k: p.read_bytes() for k, p in FILES.items()}
assert hashlib.sha256(raw["state"]).hexdigest() == "1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb"
model, state, catalogue = (json.loads(raw[k]) for k in ("model", "state", "families"))
families = [f[k] for f in catalogue["families"] for k in ("clique", "outside")]
FULL = (1 << 64) - 1
UNRESTRICTED = [FULL] * 64
deadline = time.monotonic() + 90


def bits(mask):
    while mask:
        bit = mask & -mask
        mask -= bit
        yield bit.bit_length() - 1


def transpose(rows):
    answer = [0] * 64
    for u, row in enumerate(rows):
        for v in bits(row):
            answer[v] |= 1 << u
    return answer


relations = {}
for c in model["constraints"]:
    a, b, rows = c["x"], c["y"], c["rows"]
    if a > b:
        a, b, rows = b, a, transpose(rows)
    relations[a, b] = [x & y for x, y in zip(relations.get((a, b), UNRESTRICTED), rows)]


def hall(family, domains):
    owner = {}

    def augment(i, seen):
        for w in bits(domains[i]):
            if w in seen:
                continue
            seen.add(w)
            if w not in owner or augment(owner[w], seen):
                owner[w] = i
                return True
        return False

    for i in sorted(family, key=lambda i: (domains[i].bit_count(), i)):
        if not augment(i, set()):
            return None
    removed = set()
    for root in family:
        reached, todo, free = {root}, [root], False
        while todo:
            i = todo.pop()
            for w in bits(domains[i]):
                if w not in owner:
                    free = True
                elif owner[w] not in reached:
                    reached.add(owner[w])
                    todo.append(owner[w])
        if free:
            continue
        pool = 0
        for i in reached:
            pool |= domains[i]
        assert pool.bit_count() == len(reached)
        for i in family:
            if i not in reached:
                removed.update((i, w) for w in bits(domains[i] & pool))
    return removed


def close(domains, rels):
    domains = list(domains)
    for iteration in range(100):
        if time.monotonic() > deadline:
            return {"status": "BOUNDED_STOP"}, None
        before = list(domains)
        for (a, b), rows in rels.items():
            retained, supported = 0, 0
            for u in bits(domains[a]):
                if rows[u] & domains[b]:
                    retained |= 1 << u
                    supported |= rows[u]
            domains[a] = retained
            domains[b] &= supported
            if not domains[a] or not domains[b]:
                return {"status": "DEFICIENT_BINARY", "pair": [a, b], "rounds": iteration + 1}, None
        for family in families:
            removed = hall(family, domains)
            if removed is None:
                return {"status": "DEFICIENT_HALL", "rounds": iteration + 1}, None
            for i, w in removed:
                domains[i] &= ~(1 << w)
        if before == domains:
            return {"status": "FIXED_POINT", "rounds": iteration + 1}, domains
    return {"status": "BOUNDED_STOP"}, None


def diff(before, after):
    return [[i, w] for i, (a, b) in enumerate(zip(before, after)) for w in bits(a & ~b)]


def joint(domains, rels):
    strengthened = {pair: list(rows) for pair, rows in rels.items()}
    records = []
    unary = set()
    for a in range(model["variables"] - 2):
        b, c = a + 1, a + 2
        ab = rels.get((a, b), UNRESTRICTED)
        bc = rels.get((b, c), UNRESTRICTED)
        ac = rels.get((a, c), UNRESTRICTED)
        sab, sbc, sac = ([0] * 64 for _ in range(3))
        tuples = 0
        for u in bits(domains[a]):
            for v in bits(ab[u] & domains[b]):
                ws = bc[v] & ac[u] & domains[c]
                if ws:
                    sab[u] |= 1 << v
                    sbc[v] |= ws
                    sac[u] |= ws
                    tuples += ws.bit_count()
        supported = [sum(1 << u for u in bits(domains[a]) if sab[u]),
                     sum(1 << v for v in bits(domains[b]) if sbc[v]), 0]
        for row in sac:
            supported[2] |= row
        deleted = [[i, w] for i, mask in zip((a, b, c), supported)
                   for w in bits(domains[i] & ~mask)]
        unary.update(map(tuple, deleted))
        pair_records = []
        for (x, y), original, support in (((a, b), ab, sab), ((b, c), bc, sbc), ((a, c), ac, sac)):
            removed = [(u, v) for u in bits(domains[x])
                       for v in bits(original[u] & domains[y] & ~support[u])]
            kept_rows = strengthened.setdefault((x, y), list(original))
            for u in bits(domains[x]):
                kept_rows[u] &= (FULL ^ domains[y]) | support[u]
            pair_records.append({"pair": [x, y], "unsupported_count": len(removed),
                                 "unsupported_distance_0_or_2_count": sum((u ^ v).bit_count() in (0, 2) for u, v in removed),
                                 "examples": removed[:3]})
        if deleted or any(r["unsupported_count"] for r in pair_records):
            records.append({"triple": [a, b, c], "domain_masks": [domains[i] for i in (a, b, c)],
                            "supported_triples": tuples, "unary_deletions": deleted,
                            "outer_relation_present": (a, c) in rels, "pairs": pair_records})
    return {"unary_deletions": sorted(unary), "affected_triples": records,
            "unsupported_pair_occurrences": sum(p["unsupported_count"] for t in records for p in t["pairs"])}, strengthened


distance02 = [sum(1 << v for v in range(64) if (u ^ v).bit_count() in (0, 2)) for u in range(64)]
static = {pair: list(rows) for pair, rows in relations.items()}
adjacent_distances = set()
for a in range(model["variables"] - 1):
    rows = relations.get((a, a + 1), UNRESTRICTED)
    adjacent_distances.update((u ^ v).bit_count() for u in range(64) for v in bits(rows[u]))
assert adjacent_distances == {1}, adjacent_distances
for a in range(model["variables"] - 2):
    old = static.get((a, a + 2), UNRESTRICTED)
    static[a, a + 2] = [x & y for x, y in zip(old, distance02)]

regions = []
for region in state["frontier"]:
    record = {"region_id": region["id"]}
    record["baseline"], base = close(region["domains"], relations)
    if base is not None:
        record["baseline"]["removed_values"] = diff(region["domains"], base)
        record["baseline"]["domains"] = base
        record["joint_before_static"], projected = joint(base, relations)
        record["static_closure"], narrowed = close(base, static)
        if narrowed is not None:
            record["static_closure"]["additional_removed_values"] = diff(base, narrowed)
            record["static_closure"]["domains"] = narrowed
            record["joint_after_static"], projected = joint(narrowed, static)
            record["one_joint_projection_then_existing_closure"], final = close(narrowed, projected)
            if final is not None:
                record["one_joint_projection_then_existing_closure"]["additional_removed_values"] = diff(narrowed, final)
                record["one_joint_projection_then_existing_closure"]["domains"] = final
    regions.append(record)

result = {
    "scope": "Immutable five-region snapshot; bounded matching, binary filtering and exact three-variable relation projections; no branching search or solver.",
    "inputs": {k: {"path": str(FILES[k]), "sha256": hashlib.sha256(v).hexdigest()} for k, v in raw.items()},
    "source_jobs": state["committed_jobs"], "frontier_regions": len(state["frontier"]),
    "adjacent_relation_hamming_distances": sorted(adjacent_distances),
    "omitted_rules": ["partner capacity/support", "lexicographic symmetry rules", "higher-order nogoods"],
    "regions": regions,
    "limitations": "Counts are occurrences by region/triple; pair projection can count the same pair in two triples. No Lean certificate, complete traversal, current-frontier claim or runtime benefit.",
}
output = ROOT / "data" / "joint-support-analysis.json"
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"output": str(output), "regions": [
    {"id": r["region_id"], "baseline": r["baseline"]["status"],
     "static": r.get("static_closure", {}).get("status"),
     "static_deletions": len(r.get("static_closure", {}).get("additional_removed_values", [])),
     "joint_unary": len(r.get("joint_after_static", {}).get("unary_deletions", [])),
     "joint_pairs": r.get("joint_after_static", {}).get("unsupported_pair_occurrences"),
     "joint_closure": r.get("one_joint_projection_then_existing_closure", {}).get("status"),
     "joint_closure_deletions": len(r.get("one_joint_projection_then_existing_closure", {}).get("additional_removed_values", []))}
    for r in regions]}))
