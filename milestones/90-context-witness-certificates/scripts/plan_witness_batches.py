"""Plan reusable witness-validity checks from the pinned milestone 89 payload.

No geometry is recomputed, witnesses regenerated, or proof jobs launched.
Job IDs and the core manifest are deterministic; receipt observations are a
separate timestamped snapshot. All IDs in the manifest are zero-based.
"""
from pathlib import Path
from collections import defaultdict
import datetime
import gzip
import hashlib
import json
import re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / "milestones/89-shared-cover-certification"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


pins = {}


def pinned(path):
    raw = path.read_bytes()
    pins[path.relative_to(ROOT).as_posix()] = digest(raw)
    return raw


payload_raw = pinned(OLD / "data/context-witnesses.json.gz")
uncompressed = gzip.decompress(payload_raw)
data = json.loads(uncompressed)
audit = json.loads(pinned(OLD / "data/context-witnesses-audit.json"))
assert audit["status"] == "PASS_ALL_CONTEXT_WITNESSES"
assert digest(payload_raw) == audit["payload_sha256"]
assert digest(uncompressed) == audit["payload_raw_sha256"]
assert digest(pinned(OLD / "scripts/materialize_witnesses.py")) == data["script_sha256"]
assert data["family_codes"] == ["reference", "short", "interval", "history"]
assert len(data["contexts"]) == audit["contexts"] == 791
assert len(data["classes"]) == audit["classes"] == 127
assert len(data["witness_lists"]) == 211
classes = dict(data["classes"])
assert list(classes) == list(range(127))
assert len({tuple(tuple(interval) for interval in box) for box in data["box_catalogue"]}) == len(data["box_catalogue"])
witnesses = data["witnesses"]
assert len({tuple(witness) for witness in witnesses}) == len(witnesses)
lists = data["witness_lists"]


def verify_receipt(module):
    path = OLD / "data" / (module + "-audit.json")
    receipt = json.loads(pinned(path))
    assert receipt["exit_code"] == 0 and receipt["status"].startswith("PASS_")
    for folder, ext, key in [("lean", ".lean", "source_sha256"),
                             ("build", ".olean", "olean_sha256"),
                             ("logs", ".log", "log_sha256")]:
        assert digest(pinned(OLD / folder / (module + ext))) == receipt[key]
    return {"module": module, "receipt_sha256": digest(path.read_bytes()),
            "status": receipt["status"],
            "theorem_audits": receipt.get("theorem_audits", [])}


generic = [verify_receipt(name) for name in ["ContextTransport", "SharedAssembly"]]
raw_contexts = []
base_groups = defaultdict(list)
for source_index, (block, class_id, list_id) in enumerate(data["contexts"]):
    direction, history = divmod(block, 75)
    assert 0 <= direction < 505 and 0 <= history < 75
    ws = lists[list_id]
    boxes = classes[class_id]
    assert len(ws) == len(boxes) > 0
    history_positions = [i for i, wid in enumerate(ws) if witnesses[wid][0] == 3]
    assert history_positions in [[], [0]]
    start = len(history_positions)
    assert all(witnesses[wid][0] in [0, 1, 2] for wid in ws[start:])
    assert all(0 <= gid < len(data["box_catalogue"]) for gid in boxes)
    key = (class_id, start, tuple(ws[start:]))
    row = {"source_context_index": source_index, "block_id": block,
           "direction": direction, "history": history, "class_id": class_id,
           "original_list_id": list_id, "base_key": key,
           "history_witness_id": ws[0] if start else None}
    base_groups[key].append(row)
    raw_contexts.append(row)
assert len({r["block_id"] for r in raw_contexts}) == 791

base_keys = sorted(base_groups)
base_ids = {key: i for i, key in enumerate(base_keys)}
base_lists = []
for bid, (class_id, start, ws) in enumerate(base_keys):
    stop = len(classes[class_id])
    pairs = list(zip(classes[class_id][start:stop], ws))
    assert len(pairs) == len(ws) == stop - start
    base_lists.append({"base_list_id": bid, "class_id": class_id,
                       "original_box_positions": {"start": start, "stop": stop, "step": 1},
                       "witness_ids": list(ws), "entry_count": len(ws),
                       "ordered_geometry_witness_ids_sha256": digest(canonical(pairs)),
                       "original_list_ids": sorted({r["original_list_id"] for r in base_groups[base_keys[bid]]})})

job_keys = sorted({(r["direction"], r["class_id"], base_ids[r["base_key"]]) for r in raw_contexts})
job_ids = {key: i for i, key in enumerate(job_keys)}
jobs = []
for jid, (direction, class_id, base_id) in enumerate(job_keys):
    members = [r for r in base_groups[base_keys[base_id]] if r["direction"] == direction]
    base = base_lists[base_id]
    jobs.append({"base_job_id": jid, "direction": direction, "check_history": 0,
                 "class_id": class_id, "base_list_id": base_id,
                 "entry_count": base["entry_count"],
                 "original_box_positions": base["original_box_positions"],
                 "original_list_ids": sorted({r["original_list_id"] for r in members}),
                 "context_blocks": sorted(r["block_id"] for r in members),
                 "target_histories": sorted(r["history"] for r in members),
                 "required_equations": ["entriesHistoryFree base = true", "entriesValid 0 direction base = true"]})

history_jobs = []
history_ids = {}
for row in sorted((r for r in raw_contexts if r["history_witness_id"] is not None), key=lambda r: r["block_id"]):
    block = row["block_id"]
    wid = row["history_witness_id"]
    constructor = witnesses[wid]
    assert constructor[0] == 3 and constructor[2:] == [0, 0]
    hid = len(history_jobs)
    history_ids[block] = hid
    history_jobs.append({"history_job_id": hid, "block_id": block,
                         "direction": row["direction"], "history": row["history"],
                         "class_id": row["class_id"], "original_list_id": row["original_list_id"],
                         "original_box_position": 0, "geometry_id": classes[row["class_id"]][0],
                         "witness_id": wid, "witness_constructor": constructor,
                         "required_equation": "boxWitnessValid history direction box (.history ruleIndex) = true"})

contexts = []
for row in raw_contexts:
    bid = base_ids[row["base_key"]]
    jid = job_ids[(row["direction"], row["class_id"], bid)]
    result = {key: row[key] for key in ["source_context_index", "block_id", "direction", "history", "class_id", "original_list_id"]}
    result.update(base_job_id=jid, base_list_id=bid, history_job_id=history_ids.get(row["block_id"]),
                  assembly="base_after_history_valid" if row["block_id"] in history_ids else "entries_valid_transport")
    base = base_lists[bid]
    pairs = list(zip(classes[row["class_id"]][base["original_box_positions"]["start"]:], base["witness_ids"]))
    if result["history_job_id"] is not None:
        hj = history_jobs[result["history_job_id"]]
        pairs.insert(0, (hj["geometry_id"], hj["witness_id"]))
    assert pairs == list(zip(classes[row["class_id"]], lists[row["original_list_id"]]))
    assert len(pairs) == len(classes[row["class_id"]])
    contexts.append(result)

# Rule out further merging by exact ordered entry identity within a direction.
entry_keys = []
for job in jobs:
    base = base_lists[job["base_list_id"]]
    start = base["original_box_positions"]["start"]
    entry_keys.append((job["direction"], tuple(zip(classes[job["class_id"]][start:], base["witness_ids"]))))
assert len(set(entry_keys)) == len(jobs) == 507
assert len(base_lists) == 210 and len(history_jobs) == 3
assert [(h["direction"], h["history"], h["class_id"], h["original_list_id"], h["witness_constructor"][1])
        for h in history_jobs] == [(177, 43, 85, 112, 0), (177, 70, 85, 113, 2), (180, 68, 89, 117, 1)]
assert next(r for r in contexts if r["block_id"] == 13318)["base_job_id"] == next(r for r in contexts if r["block_id"] == 13345)["base_job_id"]
assert [r["direction"] for r in contexts if r["class_id"] == 1] == [1, 3, 307, 308, 310, 312]

sharing = [{"base_list_id": bid, "base_job_ids": [j["base_job_id"] for j in jobs if j["base_list_id"] == bid],
            "directions": [j["direction"] for j in jobs if j["base_list_id"] == bid]} for bid in range(len(base_lists))]
duplicate_context_jobs = [j["base_job_id"] for j in jobs if len(j["context_blocks"]) > 1]
summary = {"contexts": 791, "classes": 127, "original_witness_lists": 211,
           "base_lists_after_removing_history_head": 210, "base_validity_jobs": 507,
           "history_validity_jobs": 3, "whole_list_jobs_total": 510,
           "base_entry_checks": sum(j["entry_count"] for j in jobs),
           "history_entry_checks": 3, "context_entry_occurrences": sum(len(classes[r["class_id"]]) for r in contexts),
           "context_nonhistory_occurrences": sum(len(classes[r["class_id"]]) - (r["history_job_id"] is not None) for r in contexts),
           "base_context_checks_saved": 791 - len(jobs),
           "base_jobs_reused_for_multiple_histories": len(duplicate_context_jobs),
           "max_contexts_per_base_job": max(len(j["context_blocks"]) for j in jobs),
           "base_list_groups_reused_across_directions": sum(len(s["directions"]) > 1 for s in sharing),
           "base_list_reuses_across_direction_jobs": len(jobs) - len(base_lists),
           "further_whole_entry_list_merges_within_direction": 0,
           "smallest_base_job_entries": min(j["entry_count"] for j in jobs),
           "largest_base_job_entries": max(j["entry_count"] for j in jobs)}
summary["entry_checks_saved_by_history_transport"] = summary["context_nonhistory_occurrences"] - summary["base_entry_checks"]
assert summary["context_entry_occurrences"] == audit["materialized_witness_occurrences"] == 543827
assert summary["context_nonhistory_occurrences"] == 543824

# Observe existing geometric receipts once, without waiting for running jobs.
observed = []
for path in sorted((OLD / "data").glob("*Checks-audit.json")):
    match = re.fullmatch(r"(Balanced|Cover|Fast)(\d{3})Checks-audit\.json", path.name)
    if match:
        module = path.name.removesuffix("-audit.json")
        receipt = verify_receipt(module)
        expected = "originalCover" + match.group(2) if match.group(1) == "Balanced" else None
        if expected:
            assert any(a["theorem"].split(".")[-1] == expected for a in receipt["theorem_audits"])
        receipt.update(class_id=int(match.group(2)), pathway=match.group(1))
        observed.append(receipt)
completed = sorted({r["class_id"] for r in observed})
ordered = sorted(jobs, key=lambda j: (j["entry_count"], j["base_job_id"]))
ready = [j for j in ordered if j["class_id"] in completed]
class1 = [r for r in contexts if r["class_id"] == 1]
core = {"format": "Witness batch plan v1; all IDs zero-based; context order is the pinned payload order",
        "base_lists": base_lists, "base_jobs": jobs, "history_jobs": history_jobs,
        "contexts": contexts, "list_sharing_across_directions": sharing,
        "base_jobs_shared_across_histories": duplicate_context_jobs,
        "class1_contexts": class1, "summary": summary,
        "semantics": {"base": "At history zero, check entriesHistoryFree and entriesValid on the unchanged class-position slice zipped with the listed witness IDs.",
                      "transport": "Use entries_valid_transport with the same direction and target history less than 75.",
                      "history": "Check the original head separately at its actual history, then use base_after_history_valid. Preserve position zero; do not append.",
                      "zip": "Reconstructed full ordered geometry/witness pairs exactly equal every original context zip; both lengths are equal.",
                      "minimality": "507 is the exact number of distinct direction-and-ordered-base-entry lists under whole-list sharing and history transport. No optimality over alternative proofs or per-entry sharing is asserted.",
                      "direction": "Identical witness-list data at different directions does not transfer validity; each direction remains a separate job."}}
script_hash = digest(Path(__file__).read_bytes())
plan = {"status": "PASS_DETERMINISTIC_WITNESS_JOB_PLAN", "core_manifest_sha256": digest(canonical(core)),
        **core, "first_job_candidates": {"smallest_global": ordered[:5], "largest_global": list(reversed(ordered[-5:])),
                                        "smallest_with_observed_geometry": ready[:5],
                                        "class1_base_job_ids": [r["base_job_id"] for r in class1]},
        "observed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "geometry_receipts_observation": observed, "observed_completed_geometric_classes": completed,
        "generic_transport_receipts": generic, "input_sha256": pins,
        "script_sha256": script_hash,
        "scope": "Deterministic planning and exact alignment audit only. No new validity equation, numeric membership theorem or global bound has been checked."}
for name, expected in pins.items():
    assert digest((ROOT / name).read_bytes()) == expected, ("input changed", name)
(HERE / "data").mkdir(parents=True, exist_ok=True)
output = HERE / "data/witness-batch-plan.json"
output.write_text(json.dumps(plan, indent=2) + "\n")

def show(job):
    return f"job {job['base_job_id']}: direction {job['direction']}, class {job['class_id']}, {job['entry_count']} entries, original lists {job['original_list_ids']}"


report = """# Witness batch plan

The pinned materialized data reduces to **507 base validity jobs and three history-head checks**, covering all **791 contexts** and all 127 geometric classes. The whole-list grouping is exact: no two remaining jobs at the same direction contain identical ordered geometry/witness pairs. This count does not assert minimum work under possible per-entry sharing or additional proof lemmas.

Every base is checked at history zero. `entries_valid_transport` then reuses its validity at the same direction and any required history below 75. The base job also requires `entriesHistoryFree = true`. There are **210 distinct base-list data records**, derived from the original 211 lists. Reusing list data across different directions does not transfer validity; the corresponding direction-specific jobs remain distinct.

The three history constructors occur at original position zero:

| Direction | History | Class | Original list | History rule | Witness ID |
| --- | --- | --- | --- | --- | --- |
| 177 | 43 | 85 | 112 | 0 | 4363 |
| 177 | 70 | 85 | 113 | 2 | 4364 |
| 180 | 68 | 89 | 117 | 1 | 4366 |

The two class 85 contexts share one identical tail job at direction 177. Their heads are checked separately. `SharedAssembly.base_after_history_valid` restores the head before the transported tail. Appending it would change the box order and cannot be substituted without a separate reordered cover proof. Class 89 similarly uses its tail and its own history head.

For every context, the script reconstructs the full ordered geometry/witness pairs from its base slice and optional head and compares them with the original zip. All lengths, class positions, original list IDs, direction/history IDs and context mappings agree. No geometry or witness validity is recomputed.

## Work counts and first jobs

"""
for key, value in summary.items():
    report += f"- `{key}`: {value}.\n"
report += "\nSmallest global job: " + show(ordered[0]) + ".\n\n"
report += "Largest global job, with deterministic tie-breaking: " + show(list(reversed(ordered[-5:]))[0]) + ".\n\n"
if ready:
    report += "Smallest job with an observed completed geometric class: " + show(ready[0]) + ".\n\n"
report += "Class 1 supplies a useful six-job integration batch: directions **1, 3, 307, 308, 310 and 312**, each with 640 entries, all at history zero. Directions 1 and 310 use original list 1; the other four use original list 3. These are two data lists and six validity checks. Their exact job IDs and original context indices are in `class1_contexts`.\n\n"
report += "## Manifest and evidence boundaries\n\n"
report += "`base_lists` records the exact witness IDs and original class-position slice `[start, stop)`, plus an ordered pair hash. `base_jobs` gives direction, history-zero equations, source lists and every receiving context. `history_jobs` preserves the original head position, geometry ID and constructor. `contexts` maps all original payload rows to these jobs. Box geometry and witness constructors are addressed by their original IDs in the hash-pinned payload. No class or list is relabelled.\n\n"
report += "Job IDs, complete mappings and the core manifest hash are deterministic. Receipt observations are separate and may change between runs. The current matching geometric receipts were observed once, without waiting: classes **" + ", ".join(map(str, completed)) + "**. This observation checks source/object/log hashes and the printed original-cover theorem where applicable; it does not independently rebuild their transitive dependencies.\n\n"
report += "The existing generic transport and head-restoration sources, objects, logs and receipts were hash-checked. No new Lean validity proof, context membership theorem, saved-row theorem or global snake bound follows from the plan. Entry counts measure batch size; they are not runtime estimates.\n\n"
report += f"- Input witness payload SHA-256: `{digest(payload_raw)}`.\n"
report += f"- Planning script SHA-256: `{script_hash}`.\n"
report += f"- Deterministic core manifest SHA-256: `{plan['core_manifest_sha256']}`.\n"
report += f"- Complete plan SHA-256: `{digest(output.read_bytes())}`.\n"
report += f"- Observation time: `{plan['observed_at_utc']}`.\n"
(HERE / "audit").mkdir(parents=True, exist_ok=True)
(HERE / "audit/witness-batch-plan.md").write_text(report)
print(json.dumps({"summary": summary, "completed_geometric_classes": completed,
                  "smallest": show(ordered[0]), "largest": show(ordered[-1]),
                  "smallest_ready": show(ready[0]) if ready else None,
                  "class1_jobs": plan["first_job_candidates"]["class1_base_job_ids"],
                  "script_sha256": script_hash, "manifest_sha256": digest(output.read_bytes()),
                  "core_sha256": plan["core_manifest_sha256"]}, indent=2))
