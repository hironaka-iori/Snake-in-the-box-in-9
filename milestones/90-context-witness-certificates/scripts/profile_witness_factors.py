"""Profile exact Boolean factors on the existing 507 base jobs and 3 heads.

This reads saved materialization only. It starts no Lean or solver process and
does not regenerate raw rule occurrences or geometric covers.
"""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PINS = {}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def raw(relative):
    value = (ROOT / relative).read_bytes()
    PINS[relative] = digest(value)
    return value


def read(relative):
    return json.loads(raw(relative))


def get(xs, i, default):
    return xs[i] if 0 <= i < len(xs) else default


def canon(xs):
    names = {}
    return [names.setdefault(x, len(names)) for x in xs]


def orient(xs, reverse):
    return xs[::-1] if reverse else xs


payload = json.loads(gzip.decompress(raw("milestones/89-shared-cover-certification/data/context-witnesses.json.gz")))
plan = read("milestones/90-context-witness-certificates/data/witness-batch-plan.json")
assert plan["status"] == "PASS_DETERMINISTIC_WITNESS_JOB_PLAN"
assert len(plan["base_jobs"]) == 507 and len(plan["history_jobs"]) == 3
assert PINS["milestones/89-shared-cover-certification/data/context-witnesses.json.gz"] == plan["input_sha256"]["milestones/89-shared-cover-certification/data/context-witnesses.json.gz"]
model = read("milestones/59-extended-share-window/extended/data/model.json")
history_data = read("milestones/67-critical-family-charge/data/full-model.json")
refs = read("milestones/85-reference-catalogue-union/data/reference-union.json")["rows"]
normal = read("milestones/81-recovered-short-rule-retention/data/normalized-rules.json")
short = [r for r in normal if r["kind"] == "caps"] + [r for r in normal if r["kind"] == "sum"]
metadata = read("milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json")
interval_cases = read("milestones/72-four-count-proof-closure/data/cases.json")
intervals = [next(r for r in interval_cases if r["number"] == n) for n in metadata["applied_cases"]]
histories = [r for r in history_data["patterns"] if r["mode"] == "exclusion"]
directions = model["extensions"]
prefixes = history_data["prefixes"]
classes = dict(payload["classes"])
assert (len(directions), len(prefixes), len(refs), len(short), len(intervals), len(histories)) == (505, 75, 1378, 40, 10, 3)
assert payload["rule_sources"]["reference"] == [[r["source_catalogue"], r["source_index"]] for r in refs]
assert payload["rule_sources"]["short"] == [[r["number"], r["source"]] for r in short]
assert payload["rule_sources"]["interval"] == [r["number"] for r in intervals]
assert payload["rule_sources"]["history"] == [[r["signature"], [5, 3, 5][i]] for i, r in enumerate(histories)]
for relative, expected in payload["input_sha256"].items():
    if relative in PINS:
        assert PINS[relative] == expected
for relative in ["milestones/88-retention-diagram-certificate/lean/BoxWitness.lean",
                 "milestones/81-recovered-short-rule-retention/lean/GuardTransfer.lean",
                 "milestones/81-recovered-short-rule-retention/lean/PositionTransfer.lean",
                 "milestones/89-shared-cover-certification/lean/ContextTransport.lean"]:
    raw(relative)


def decoded_index(ds):
    # Lean List.idxOf returns the list length if the element is absent.
    return next((i for i, value in enumerate(directions) if value == ds), len(directions))


def direct(q, di, box, witness):
    """Direct interpretation of the original BoxWitness Boolean definition."""
    if not (len(box) == 6 and q < 75 and di < 505):
        return False
    ds = get(directions, di, [])
    family, ki, offset, reverse = witness
    if family == 0:
        key = get(refs, ki, {"directions": [], "symbols": []})
        width = len(key["symbols"])
        return (ki < len(refs) and 2 <= width and offset + width <= 6
                and canon(orient(ds[offset + 2:offset + width + 3], reverse)) == key["directions"]
                and all(get(box, offset + i, [1, 6]) == [v, v]
                        for i, v in enumerate(orient(key["symbols"], reverse))))
    if family == 1:
        rule = get(short, ki, {"dirs": [], "kind": "caps", "caps": []})
        length = len(rule["dirs"])
        positions = [p for p, _ in rule["caps"]] if rule["kind"] == "caps" else rule["positions"]
        placed = [offset + (max(0, length - j) if reverse else j) for j in positions]
        upper = [get(box, max(0, j - 3), [1, 6])[1] for j in placed]
        encoded = (all(v <= cap for v, (_, cap) in zip(upper, rule["caps"])) if rule["kind"] == "caps"
                   else sum(upper) <= rule["cap"] and all(v < 6 for v in upper))
        return (ki < len(short) and offset < 10 and offset + length <= 9
                and all(3 <= j <= 8 for j in placed)
                and canon(orient(ds[offset:offset + length], reverse)) == rule["dirs"] and encoded)
    if family == 2:
        key = get(intervals, ki, {"dirs": [], "bounds": []})
        positions = [offset + (max(0, 3 - i) if reverse else i) for i in range(len(key["bounds"]))]
        return (ki < len(intervals) and offset < 3 and len(key["bounds"]) == 4
                and canon(orient(ds[offset + 2:offset + 7], reverse)) == key["dirs"]
                and all(j < 6 and lo <= get(box, j, [1, 6])[0] and get(box, j, [1, 6])[1] <= hi
                        for j, (lo, hi) in zip(positions, key["bounds"])))
    assert family == 3
    rule = get(histories, ki, {"signature": []})
    position = get([5, 3, 5], ki, 0)
    hist = get(prefixes, q, []) + [decoded_index(ds)]
    return (ki < len(histories) and position < 6 and len(hist) >= 3
            and hist[max(0, len(hist) - 3):] == rule["signature"]
            and get(box, position, [1, 6])[1] <= 2)


def descriptors(q, di, box, witness):
    """Four exact factors: outer guard, catalogue guard, shape, box/count.

    Shape keys omit reference count-symbol values and catalogue indices, while
    retaining family, direction, slice length/offset, orientation and pattern.
    Box factors omit unused coordinates but retain each tested actual interval.
    """
    family, ki, offset, reverse = witness
    ds = get(directions, di, [])
    outer = {"box_length": len(box), "history": q, "direction": di,
             "atoms": [["eq", len(box), 6], ["lt", q, 75], ["lt", di, 505]]}
    guard = {"family": family, "catalogue_index": ki, "offset": offset, "atoms": []}
    shape = {"kind": "direction", "family": family, "direction": di, "source_word": ds,
             "reverse": bool(reverse)}
    if family == 0:
        key = get(refs, ki, {"directions": [], "symbols": []})
        width = len(key["symbols"])
        guard.update(catalogue_length=len(refs), symbol_length=width,
                     atoms=[["lt", ki, len(refs)], ["le", 2, width], ["le", offset + width, 6]])
        shape.update(drop=offset + 2, take=width + 1, pattern=key["directions"])
        bounds = {"kind": "reference_singletons", "tests": [
            {"position": offset + i, "actual_bounds": get(box, offset + i, [1, 6]), "symbol": v}
            for i, v in enumerate(orient(key["symbols"], reverse))]}
    elif family == 1:
        rule = get(short, ki, {"dirs": [], "kind": "caps", "caps": []})
        length = len(rule["dirs"])
        positions = [p for p, _ in rule["caps"]] if rule["kind"] == "caps" else rule["positions"]
        placed = [offset + (max(0, length - j) if reverse else j) for j in positions]
        guard.update(catalogue_length=len(short), direction_length=length, reverse=bool(reverse),
                     original_positions=positions, oriented_path_positions=placed,
                     atoms=[["lt", ki, len(short)], ["lt", offset, 10], ["le", offset + length, 9]]
                     + [[op, a, b] for j in placed for op, a, b in [("le", 3, j), ("le", j, 8)]])
        shape.update(drop=offset, take=length, pattern=rule["dirs"])
        tests = [{"position": max(0, j - 3), "actual_bounds": get(box, max(0, j - 3), [1, 6])} for j in placed]
        if rule["kind"] == "caps":
            for t, (_, cap) in zip(tests, rule["caps"]):
                t["cap"] = cap
            bounds = {"kind": "short_caps", "tests": tests}
        else:
            bounds = {"kind": "short_sum", "tests": tests, "sum_cap": rule["cap"], "each_upper_strictly_below": 6}
    elif family == 2:
        key = get(intervals, ki, {"dirs": [], "bounds": []})
        guard.update(catalogue_length=len(intervals), bound_count=len(key["bounds"]),
                     atoms=[["lt", ki, len(intervals)], ["lt", offset, 3], ["eq", len(key["bounds"]), 4]])
        shape.update(drop=offset + 2, take=5, pattern=key["dirs"])
        tests = []
        for i, target in enumerate(key["bounds"]):
            j = offset + (max(0, 3 - i) if reverse else i)
            tests.append({"position": j, "position_limit": 6, "actual_bounds": get(box, j, [1, 6]), "target_bounds": target})
        bounds = {"kind": "interval", "tests": tests}
    else:
        assert family == 3
        rule = get(histories, ki, {"signature": []})
        position = get([5, 3, 5], ki, 0)
        guard.update(catalogue_length=len(histories), count_position=position,
                     atoms=[["lt", ki, len(histories)], ["lt", position, 6]])
        shape = {"kind": "history", "history": q, "direction": di, "source_word": ds,
                 "decoded_idxOf": decoded_index(ds), "source_prefix": get(prefixes, q, []),
                 "required_minimum_length": 3, "suffix_length": 3, "pattern": rule["signature"]}
        bounds = {"kind": "history_upper", "tests": [{"position": position, "actual_bounds": get(box, position, [1, 6]), "cap": 2}]}
    return outer, guard, shape, bounds


def atoms_true(desc):
    for op, a, b in desc["atoms"]:
        if not {"eq": a == b, "lt": a < b, "le": a <= b}[op]:
            return False
    return True


def shape_true(desc):
    if desc["kind"] == "direction":
        word = desc["source_word"]
        piece = word[desc["drop"]:desc["drop"] + desc["take"]]
        return canon(orient(piece, desc["reverse"])) == desc["pattern"]
    idx = decoded_index(desc["source_word"])
    assert idx == desc["decoded_idxOf"]
    hist = desc["source_prefix"] + [idx]
    n = desc["suffix_length"]
    return len(hist) >= desc["required_minimum_length"] and hist[max(0, len(hist) - n):] == desc["pattern"]


def box_true(desc):
    kind, tests = desc["kind"], desc["tests"]
    if kind == "reference_singletons":
        return all(t["actual_bounds"][0] == t["symbol"] and t["actual_bounds"][1] == t["symbol"] for t in tests)
    if kind in ["short_caps", "history_upper"]:
        return all(t["actual_bounds"][1] <= t["cap"] for t in tests)
    if kind == "short_sum":
        upper = [t["actual_bounds"][1] for t in tests]
        return sum(upper) <= desc["sum_cap"] and all(v < desc["each_upper_strictly_below"] for v in upper)
    assert kind == "interval"
    return all(t["position"] < t["position_limit"] and t["target_bounds"][0] <= t["actual_bounds"][0]
               and t["actual_bounds"][1] <= t["target_bounds"][1] for t in tests)


names = ["outer_guards", "catalogue_guards", "shape_factors", "box_factors"]
tables = {name: [] for name in names}
ids = {name: {} for name in names}
evaluators = [atoms_true, atoms_true, shape_true, box_true]
family_counts = Counter()
family_shapes = {i: set() for i in range(4)}
family_boxes = {i: set() for i in range(4)}
family_original_shapes = {i: set() for i in range(4)}
full_box_witness = set()
full_direction_box_witness = set()
base_maps = []
head_maps = []
count = 0
original_hash = hashlib.sha256()
factored_hash = hashlib.sha256()


def entry(q, di, geometry_id, witness_id, location):
    global count
    b = payload["box_catalogue"][geometry_id]
    w = payload["witnesses"][witness_id]
    ds = descriptors(q, di, b, w)
    factor_ids = []
    factor_values = []
    for name, descriptor, evaluator in zip(names, ds, evaluators):
        encoded = compact(descriptor)
        if encoded not in ids[name]:
            ids[name][encoded] = len(tables[name])
            tables[name].append({"descriptor": descriptor, "value": evaluator(descriptor), "uses": 0, "first_occurrence": location})
        fid = ids[name][encoded]
        factor_ids.append(fid)
        record = tables[name][fid]
        record["uses"] += 1
        factor_values.append(record["value"])
    original = direct(q, di, b, w)
    factored = all(factor_values)
    assert original == factored, (location, w, original, factor_values)
    assert original, ("saved witness invalid", location, w)
    original_hash.update(bytes([original]))
    factored_hash.update(bytes([factored]))
    family_counts[w[0]] += 1
    family_shapes[w[0]].add(factor_ids[2])
    family_boxes[w[0]].add(factor_ids[3])
    family_original_shapes[w[0]].add((q if w[0] == 3 else 0, di, *w[1:]))
    full_box_witness.add((geometry_id, witness_id))
    full_direction_box_witness.add((q if w[0] == 3 else 0, di, geometry_id, witness_id))
    count += 1
    return factor_ids


for job in plan["base_jobs"]:
    base = plan["base_lists"][job["base_list_id"]]
    start, stop = base["original_box_positions"]["start"], base["original_box_positions"]["stop"]
    geometries = classes[job["class_id"]][start:stop]
    assert len(geometries) == len(base["witness_ids"]) == job["entry_count"]
    entries = [entry(0, job["direction"], gid, wid, ["base", job["base_job_id"], start + i])
               for i, (gid, wid) in enumerate(zip(geometries, base["witness_ids"]))]
    base_maps.append({"base_job_id": job["base_job_id"], "original_start_position": start, "factors": entries})
for job in plan["history_jobs"]:
    factor_ids = entry(job["history"], job["direction"], job["geometry_id"], job["witness_id"], ["history", job["history_job_id"], 0])
    head_maps.append({"history_job_id": job["history_job_id"], "factors": factor_ids})
assert count == plan["summary"]["base_entry_checks"] + 3 == 357823
assert original_hash.hexdigest() == factored_hash.hexdigest()
by_family = []
for family in range(4):
    by_family.append({"family": family, "name": payload["family_codes"][family], "occurrences": family_counts[family],
                      "unique_catalogue_indexed_shape_calls": len(family_original_shapes[family]),
                      "unique_normalized_shape_tests": len(family_shapes[family]),
                      "unique_box_condition_tests": len(family_boxes[family])})
summary = {"planned_base_jobs": 507, "history_heads": 3, "planned_entries_compared": count,
           "all_original_values_true": True, "all_factored_values_equal": True,
           "factor_counts": {name: len(rows) for name, rows in tables.items()},
           "unique_box_witness_pairs": len(full_box_witness),
           "unique_direction_history_box_witness_calls": len(full_direction_box_witness),
           "shape_factor_evaluations_saved_vs_occurrences": count - len(tables["shape_factors"]),
           "box_factor_evaluations_saved_vs_occurrences": count - len(tables["box_factors"]),
           "by_family": by_family, "original_boolean_stream_sha256": original_hash.hexdigest(),
           "factored_boolean_stream_sha256": factored_hash.hexdigest()}
for name, expected in PINS.items():
    assert digest((ROOT / name).read_bytes()) == expected, ("changed input", name)
script_hash = digest(Path(__file__).read_bytes())
result = {"status": "PASS_PLANNED_WITNESS_FACTOR_PROFILE", "summary": summary,
          "format": "Factor IDs are zero-based. Each entry map is [outer_guard_id,catalogue_guard_id,shape_id,box_id].",
          "factor_evaluation": "The exact original Boolean is the conjunction of all four factors. Outer/catalogue atoms retain their explicit integer comparisons. Direction shapes canonically relabel the oriented drop/take slice. History shapes recompute original extensions.idxOf, append it to the prefix, enforce length>=3, and compare the last three IDs. Box tests retain actual tested bounds, positions, symbols/caps and the strict sum saturation guard.",
          "normalization": "Keep family, actual direction, offset, take length, reversal and target pattern in direction-shape descriptors. Omit reference catalogue index and count-symbol values only from shape descriptors; retain them in catalogue guards and box tests. Omit unused coordinates from box descriptors. Preserve list order and duplicate positions. No directions, patterns or geometries are merged by graph symmetry.",
          "tables": tables, "base_job_maps": base_maps, "history_head_maps": head_maps,
          "recommendation": "A bounded reference-shape reuse pilot is justified before the full 507-job batch: references account for 338697 of 357823 planned entries and their 337485 catalogue-indexed shape calls reduce to 12560 normalized shape-only tests. Require a same-class successful Lean comparison before adopting it for the full batch. A two-factor compatibility/box split that retains the catalogue index in compatibility does not by itself obtain this shape sharing; it needs an additional normalized shape expression or lemma. Preserve the existing direct validator path if proof assembly overhead outweighs reuse.",
          "input_sha256": PINS, "script_sha256": script_hash,
          "scope": "Proposed proof-factorization opportunity and exhaustive computational equality on the saved planned entries only; no new Lean theorem, global result, or measured speedup. Every saved entry is true, so this is not a general equivalence proof or a negative-case test suite."}
out = HERE / "data/witness-factor-profile.json"
out.write_bytes(compact(result) + b"\n")
report = """# Witness factor profile

The existing validator can be represented on the saved planned entries by four explicit factors: the outer bounds, the catalogue/placement guards, the direction or history shape test, and the box/count test. Every one of the **357,823 planned entries** was evaluated directly and compared with the conjunction of these factors. All comparisons agree and all original entries are true.

This is a proposed proof-factorization opportunity. It is not a new Lean equivalence theorem or a measured speed improvement. All tested saved entries are valid; the computational comparison does not establish equivalence on arbitrary invalid inputs.

## Exact counts

| Family | Planned occurrences | Unique catalogue-indexed shape calls | Unique normalized shape tests | Unique box tests |
| --- | --- | --- | --- | --- |
"""
for row in by_family:
    report += f"| {row['name']} | {row['occurrences']} | {row['unique_catalogue_indexed_shape_calls']} | {row['unique_normalized_shape_tests']} | {row['unique_box_condition_tests']} |\n"
report += "\nFactor catalogue sizes: " + ", ".join(f"{k}: {v}" for k, v in summary["factor_counts"].items()) + ".\n\n"
report += f"There are **{summary['unique_box_witness_pairs']:,}** unique full box/witness pairs and **{summary['unique_direction_history_box_witness_calls']:,}** distinct direction/history/box/witness calls in the plan. Normalizing only the tested box conditions gives **{len(tables['box_factors']):,}** distinct box factors. The full descriptor tables include usage counts and first-occurrence provenance.\n\n"
report += "## Conditions retained\n\n"
report += "The outer factor retains box length 6, history below 75 and direction below 505. Catalogue factors retain the exact index/length comparisons and placement constraints. Reference shape descriptors keep the actual direction word, drop offset, slice length, reversal and target pattern; only the count-symbol values and catalogue index are removed from that shape key. The omitted values remain in the box/count factor and catalogue guard. Thus keys sharing a direction pattern can reuse shape evidence without sharing their distinct count assertions.\n\n"
report += "Reference box factors check both interval endpoints equal the oriented symbol. Short cap factors retain each tested upper bound and its cap. Short sum factors retain every position, multiplicity, actual interval, total cap and the strict condition that every tested upper endpoint is below 6. Interval factors retain the reversed position computation, its bound below 6 and both containment inequalities. No cap-6 or saturation exception is dropped.\n\n"
report += "History descriptors retain the source word and prefix, recompute `extensions.idxOf` from the original direction table, append the decoded index, require length at least three and compare the final three IDs. The decoded result is recorded explicitly and checked. The three history catalogue/box tests retain their rule indices, count positions and upper cap 2. Natural subtraction is truncated at zero exactly where used by the Lean definitions.\n\n"
report += "## Reproduction and scope\n\n"
report += "Run `scripts/profile_witness_factors.py` to reproduce the profile. It consumes the existing pinned materialization and 507-job plan, reads catalogue data in their checked ordering, and validates their source mappings. It does not regenerate rule occurrences or geometric covers. Every entry map records four factor IDs in the declared order and preserves the original class position. Together with the hash-pinned source plan and payload, these maps reconstruct the original Boolean test without loss of guards.\n\n"
report += "A subsequent Lean implementation would still need generic factorization lemmas, exact descriptor-to-source correspondences, checked concrete factors and assembly for each planned entry. Counts indicate repeated work that may be shared; compilation cost and proof overhead were not measured.\n\n"
report += "## Recommendation before the complete batch\n\n"
report += "A bounded reference-shape reuse pilot is justified before committing the entire 507-job batch. References account for 338,697 of the 357,823 planned entries, about 94.7 percent. Their 337,485 catalogue-indexed shape calls can be expressed using 12,560 normalized shape-only tests. This is a count of distinct predicates, not a runtime speedup estimate. The first comparison should prove the same class 1 statement with the same trusted assumptions and record completed check times for both routes. Adopt the factor route only if that comparison supports it; the existing direct route remains available.\n\n"
report += "A compatibility/box split alone does not ensure the large shape reduction. If its compatibility factor still includes the catalogue index, the reference compatibility obligations remain indexed by those 337,485 calls. Reusing the 12,560 shapes requires an additional shape-only expression or a lemma reducing each catalogue-dependent match to the normalized direction, slice, orientation and target pattern. The separate 2,329 catalogue guards must still be supplied. Combining the profile's outer and catalogue guards with shape conditions, or moving box length or interval position bounds between factors, preserves the conjunction but changes which individual factor IDs can be reused.\n\n"
report += f"- Script SHA-256: `{script_hash}`.\n- Profile SHA-256: `{digest(out.read_bytes())}`.\n"
report += f"- Original and factored Boolean stream SHA-256: `{original_hash.hexdigest()}`.\n"
report += "- All input pins, factor descriptors, multiplicities and entry maps are stored in the JSON profile.\n"
(HERE / "audit/witness-factor-profile.md").write_text(report)
print(json.dumps({"summary": summary, "script_sha256": script_hash,
                  "profile_sha256": digest(out.read_bytes()), "profile_bytes": out.stat().st_size}, indent=2))
