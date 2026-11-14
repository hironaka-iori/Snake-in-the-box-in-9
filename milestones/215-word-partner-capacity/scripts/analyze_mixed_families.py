"""Bounded read-only analysis of the frozen case22 model and transferred state."""
import hashlib
import json
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "data" / "case-22"
INPUTS = {
    "model": CASE / "model.json",
    "state": CASE / "transfer214-state.json",
    "families": CASE / "support-constraints.json",
}
data = {name: json.loads(path.read_text(encoding="utf-8"))
        for name, path in INPUTS.items()}
model, state, families = data["model"], data["state"], data["families"]["families"]
visits = [set() for _ in range(model["variables"])]
for base, group in zip(model["z"], model["group"]):
    visits[group].add(base)
FULL = (1 << 64) - 1
diagonal = {}
for constraint in model["constraints"]:
    pair = tuple(sorted((constraint["x"], constraint["y"])))
    mask = sum(1 << w for w, row in enumerate(constraint["rows"])
               if row & (1 << w))
    diagonal[pair] = diagonal.get(pair, FULL) & mask


def union_masks(domains, indices):
    result = 0
    for i in indices:
        result |= domains[i]
    return result


def hall_scan(indices, domains):
    """One deterministic matching and tight-closure pass; no branching search."""
    owner = {}

    def augment(i, seen):
        bits = domains[i]
        while bits:
            bit = bits & -bits
            bits -= bit
            w = bit.bit_length() - 1
            if w in seen:
                continue
            seen.add(w)
            if w not in owner or augment(owner[w], seen):
                owner[w] = i
                return True
        return False

    for i in sorted(indices, key=lambda i: (domains[i].bit_count(), i)):
        if not augment(i, set()):
            return {"deficient": True, "removals": [], "tight_count": 0}
    removals = set()
    tight = set()
    for root in indices:
        reached = {root}
        todo = [root]
        free_reached = False
        while todo:
            i = todo.pop()
            bits = domains[i]
            while bits:
                bit = bits & -bits
                bits -= bit
                w = bit.bit_length() - 1
                if w not in owner:
                    free_reached = True
                    continue
                j = owner[w]
                if j not in reached:
                    reached.add(j)
                    todo.append(j)
        if free_reached:
            continue
        pool = union_masks(domains, reached)
        if pool.bit_count() != len(reached):
            raise RuntimeError("A proposed tight closure failed its explicit size check")
        tight.add(tuple(sorted(reached)))
        for i in indices:
            if i not in reached:
                bits = domains[i] & pool
                while bits:
                    bit = bits & -bits
                    bits -= bit
                    removals.add((i, bit.bit_length() - 1))
    return {"deficient": False, "removals": sorted(removals),
            "tight_count": len(tight)}


maximal = []
geometry = []
for parity in (0, 1):
    ids = [i for i in range(model["variables"]) if i % 2 == parity]
    multi = [i for i in ids if len(visits[i]) > 1]
    singles = [[i for i in ids if visits[i] == {corner}] for corner in range(4)]
    parity_mask = sum(1 << w for w in range(64) if w.bit_count() % 2 == parity)
    mismatches = []
    edges = 0
    for pos, i in enumerate(ids):
        for j in ids[pos + 1:]:
            model_conflict = not (diagonal.get((i, j), FULL) & parity_mask)
            geometry_conflict = not (
                len(visits[i]) == len(visits[j]) == 1
                and next(iter(visits[i])) ^ next(iter(visits[j])) == 3)
            edges += model_conflict
            if model_conflict != geometry_conflict:
                mismatches.append([i, j, model_conflict, geometry_conflict])
    entries = []
    for a in (0, 3):
        for b in (1, 2):
            entry = {"parity": parity, "corners": [a, b],
                     "indices": sorted(multi + singles[a] + singles[b])}
            entry["size"] = len(entry["indices"])
            maximal.append(entry)
            entries.append(entry)
    geometry.append({"parity": parity, "intervals": len(ids),
                     "multi_count": len(multi),
                     "singleton_counts": list(map(len, singles)),
                     "model_conflict_edges": edges,
                     "geometry_mismatches": mismatches,
                     "maximal_families": entries})

baseline = [f[key] for f in families for key in ("clique", "outside")]
deadline = time.monotonic() + 30


def baseline_closure(initial):
    """Bounded four-family Hall and binary arc filtering, without branching."""
    domains = list(initial)
    for iteration in range(100):
        if time.monotonic() > deadline:
            return {"status": "BOUNDED_STOP", "iterations": iteration}, None
        before = list(domains)
        for c in model["constraints"]:
            x, y, rows = c["x"], c["y"], c["rows"]
            retained = 0
            supported = 0
            bits = domains[x]
            while bits:
                bit = bits & -bits
                bits -= bit
                row = rows[bit.bit_length() - 1]
                if row & domains[y]:
                    retained |= bit
                    supported |= row
            domains[x] = retained
            domains[y] &= supported
            if not domains[x] or not domains[y]:
                return {"status": "DEFICIENT_BINARY", "iterations": iteration + 1}, None
        for family in baseline:
            scan = hall_scan(family, domains)
            if scan["deficient"]:
                return {"status": "DEFICIENT_HALL", "iterations": iteration + 1}, None
            for i, w in scan["removals"]:
                domains[i] &= ~(1 << w)
        if domains == before:
            return {"status": "FIXED_POINT", "iterations": iteration + 1,
                    "removed_value_count": sum((a & ~b).bit_count()
                                               for a, b in zip(initial, domains))}, domains
    return {"status": "BOUNDED_STOP", "iterations": 100}, None


regions = []
for region in state["frontier"]:
    domains = region["domains"]
    old = [hall_scan(f, domains) for f in baseline]
    new = [hall_scan(f["indices"], domains) for f in maximal]
    old_removed = {tuple(item) for scan in old for item in scan["removals"]}
    new_removed = {tuple(item) for scan in new for item in scan["removals"]}
    closure, closed = baseline_closure(domains)
    if closed is not None:
        mixed_after = [hall_scan(f["indices"], closed) for f in maximal]
        after_removed = {tuple(item) for scan in mixed_after for item in scan["removals"]}
        closure.update({
            "initial_additional_values_still_present": sorted(
                (i, w) for i, w in new_removed - old_removed if closed[i] & (1 << w)),
            "mixed_deficient_after_baseline_closure": any(s["deficient"] for s in mixed_after),
            "mixed_additional_removals_after_baseline_closure": sorted(after_removed),
        })
    regions.append({
        "region_id": region["id"],
        "baseline_deficient": any(s["deficient"] for s in old),
        "mixed_deficient": any(s["deficient"] for s in new),
        "baseline_removed_value_count": len(old_removed),
        "mixed_removed_value_count": len(new_removed),
        "additional_removed_values": sorted(new_removed - old_removed),
        "four_family_binary_closure": closure,
        "family_scans": [
            {"parity": f["parity"], "corners": f["corners"], **s}
            for f, s in zip(maximal, new)],
    })

result = {
    "scope": "Frozen-state matching/tight-closure analysis and bounded branch-free four-family/binary fixed point; no solver or search.",
    "inputs": {name: {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
               for name, path in INPUTS.items()},
    "source_jobs": state["committed_jobs"],
    "frontier_regions": len(state["frontier"]),
    "geometry": geometry,
    "regions": regions,
    "summary": {
        "baseline_deficient_regions": sum(r["baseline_deficient"] for r in regions),
        "mixed_deficient_regions": sum(r["mixed_deficient"] for r in regions),
        "regions_with_additional_removals": sum(bool(r["additional_removed_values"]) for r in regions),
        "additional_removed_value_occurrences": sum(len(r["additional_removed_values"]) for r in regions),
    },
    "limitation": "Native saved-data analysis, not a Lean certificate or current-frontier result.",
}
output = ROOT / "data" / "mixed-family-analysis.json"
output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"output": str(output), "summary": result["summary"],
                  "geometry_mismatches": [len(g["geometry_mismatches"]) for g in geometry]}))
