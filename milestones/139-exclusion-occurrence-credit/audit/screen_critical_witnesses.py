"""Read-only witness-input screen of the completed profile's critical first row."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    started = time.monotonic()
    pins = {}

    def read(rel):
        raw = (ROOT / rel).read_bytes()
        pins[rel] = sha(raw)
        return raw.decode("utf-8-sig")

    prior_rel = "milestones/138-seven-cycle-endpoints/data/witness-screen.json"
    prior = json.loads(read(prior_rel))
    checker_rel = "milestones/138-seven-cycle-endpoints/audit/screen_witnesses.py"
    read(checker_rel)
    assert pins[checker_rel] == prior["script_sha256"]
    spec = importlib.util.spec_from_file_location("checked_witness_screen138", ROOT / checker_rel)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    result_rel = "milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/results.json"
    graph = json.loads(read(result_rel))
    profile = next(x for x in graph["profiles"] if x["profile"] == "completed")
    row = profile["cycle"][0]
    assert len(profile["cycle"]) == 5
    assert row["directions"] == [0, 1, 2, 0, 3, 4, 0, 5, 4]
    assert row["counts"] == [3, 3, 5, 4, 5, 3]
    assert [row["count_code"] // 6**j % 6 + 1 for j in range(5, -1, -1)] == row["counts"]
    assert checker.canon(row["directions"][-6:]) == (0, 1, 2, 0, 3, 2)
    targets = [dict(kind="full_nine", width=9, offsets=list(range(3, 9)),
                    directions=row["directions"], counts=row["counts"]),
               dict(kind="canonical_six_suffix", width=6, offsets=list(range(1, 6)),
                    directions=list(checker.canon(row["directions"][-6:])), counts=row["counts"][1:])]
    source_cache = {}
    reports = []
    unique_paths = set()
    for old in prior["witnesses"]:
        aliases = old["source_entries"]
        source = aliases[0]
        rel, key = source["source"], source["source_entry"]
        if rel not in source_cache:
            source_cache[rel] = read(rel)
        assert pins[rel] == source["source_sha256"]
        assert pins[rel] == prior["source_files_sha256"][rel]
        if rel.endswith(".lean"):
            body = re.search(r"def " + re.escape(key) + r" : Array Nat := #\[([^]]+)\]", source_cache[rel]).group(1)
            vertices = [int(v) for v in body.split(",")]
        else:
            data = json.loads(source_cache[rel])
            vertices = data[key]["vertex_sequence"] if type(key) is int else data[key]
        assert tuple(vertices) not in unique_paths
        unique_paths.add(tuple(vertices))
        assert sha(json.dumps(vertices, separators=(",", ":")).encode("ascii")) == old["vertex_sequence_sha256"]
        directions, alpha, pairs = checker.validate(vertices)
        assert pairs == old["pairs_checked"]
        m = len(vertices) - 1
        stats = {t["kind"]: dict(shape_matches=0, exact_matches=0) for t in targets}
        matches = []
        for reverse in (False, True):
            v = list(reversed(vertices)) if reverse else vertices
            d = list(reversed(directions)) if reverse else directions
            a = {k: alpha[m-k] for k in range(1, m)} if reverse else alpha
            for target in targets:
                for start in range(m - target["width"] + 1):
                    if checker.canon(d[start:start + target["width"]]) != checker.canon(target["directions"]):
                        continue
                    stats[target["kind"]]["shape_matches"] += 1
                    if [a[start + k] for k in target["offsets"]] != target["counts"]:
                        continue
                    stats[target["kind"]]["exact_matches"] += 1
                    record = checker.window_record(v, d, a, start, target["width"], target["offsets"], reverse)
                    record.update(target=target["kind"], actual_191_edge_witness=(m == 191),
                        translated_vertices=[x ^ v[start] for x in record["vertices"]])
                    matches.append(record)
        reports.append(dict(source_entries=aliases, vertex_sequence_sha256=old["vertex_sequence_sha256"],
            edges=m, actual_191_edge_witness=m == 191, induced_and_distinct=True,
            pairs_checked=pairs, internal_counts_crosschecked=len(alpha),
            target_statistics=stats, qualifying_windows=matches))
    assert len(reports) == 135
    totals = {t["kind"]: dict(
        shape_matches=sum(r["target_statistics"][t["kind"]]["shape_matches"] for r in reports),
        exact_matches=sum(r["target_statistics"][t["kind"]]["exact_matches"] for r in reports),
        witnesses_with_exact_matches=sum(r["target_statistics"][t["kind"]]["exact_matches"] > 0 for r in reports),
        exact_matches_in_191_edge_witnesses=sum(r["target_statistics"][t["kind"]]["exact_matches"]
            for r in reports if r["actual_191_edge_witness"])) for t in targets}
    examples = {}
    for target in targets:
        choices = [(r, w) for r in reports for w in r["qualifying_windows"] if w["target"] == target["kind"]]
        choices.sort(key=lambda rw: (not rw[0]["actual_191_edge_witness"], rw[1]["orientation"] != "forward",
                                    rw[1]["oriented_start"], rw[0]["edges"]))
        if choices:
            r, w = choices[0]
            examples[target["kind"]] = dict(source_entries=r["source_entries"], edges=r["edges"],
                vertex_sequence_sha256=r["vertex_sequence_sha256"], window=w)
    out = dict(status="FINITE_ACTUAL_WITNESS_SCREEN_COMPLETE", targets=targets,
        source_profile="completed", source_cycle_rows=5, source_cycle_mean=profile["mean"],
        witnesses_checked=len(reports), unordered_vertex_pairs_checked=sum(r["pairs_checked"] for r in reports),
        internal_counts_crosschecked=sum(r["internal_counts_crosschecked"] for r in reports),
        totals=totals, minimal_verified_examples=examples, witnesses=reports,
        source_files_sha256=pins, script_sha256=sha(Path(__file__).read_bytes()), seconds=time.monotonic()-started,
        semantics="Exact integer counts, both path orientations. Full nine-transition counts at offsets3..8; last-six suffix counts at offsets1..5. Reversal uses the reversed full path and reindexes centres.",
        scope="Fresh independent path/count validation using the pinned138 checker. Source witnesses and prior files are unchanged. No SAT, Lean, or full-graph computation. A match refutes its ordinary universal local exclusion; it does not realize the entire critical cycle or establish an empty-square charge.")
    (HERE / "data/critical-witness-screen.json").write_text(json.dumps(out, indent=2)+"\n", encoding="utf-8")
    lines = ["# New critical-row screen on saved actual snakes", "",
        f"Fresh validation checked {len(reports)} distinct actual snakes, {out['unordered_vertex_pairs_checked']} unordered vertex pairs, and {out['internal_counts_crosschecked']} internal counts. The witness source hashes agree with the frozen milestone138 screen.", "",
        "| Target | Shape-only candidates | Exact matches | Witnesses with matches | Exact matches in 191-edge snakes |",
        "| --- | --- | --- | --- | --- |"]
    for target in targets:
        t = totals[target["kind"]]
        lines.append(f"| {target['kind']} | {t['shape_matches']} | {t['exact_matches']} | {t['witnesses_with_exact_matches']} | {t['exact_matches_in_191_edge_witnesses']} |")
    lines += ["", "The nine-direction target is 012034054 with exact counts (3,3,5,4,5,3) at positions 3 through 8. Its last six transitions have canonical shape 012032 and exact five-centre counts (3,5,4,5,3). Both complete path orientations were tested; full-nine reversal uses the newly oriented positions 3 through 8.", ""]
    for target in targets:
        key = target["kind"]
        if key not in examples:
            lines += [f"No exact match was found for {key}. This finite empty screen is inconclusive about a universal exclusion.", ""]
            continue
        e = examples[key]
        w = e["window"]
        source = e["source_entries"][0]
        lines += [f"The ordinary universal exclusion of {key} is false. A verified {e['edges']}-edge actual snake in `{source['source']}`, entry `{source['source_entry']}`, contains it at oriented start {w['oriented_start']} ({w['orientation']}).",
            f"The window vertices are `{w['vertices']}`. The actual directions are `{w['directions']}` and the exact counts are `{w['counts']}`. The global endpoints in this orientation are `{w['endpoints']}`. Centre-to-endpoint Hamming distances, in count order, are `{w['centre_endpoint_distances']}`.", ""]
    if examples:
        lines += ["Matching contexts are available for testing additional empty-square charge. Their existence alone gives no positive charge estimate; the screen computes singleton-square counts and endpoint distances only. A stronger condition using more context may remain possible.", ""]
    lines += ["The JSON preserves every qualifying window, original path indices, actual and translated snippets, exact counts, endpoints, source entries and hashes. The counts depend on the complete pinned path; a snippet alone does not certify them. No solver, Lean process, or full-graph evaluator was run, and no global upper bound follows from the screen.", ""]
    (HERE / "audit/critical-witness-screen.md").write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps(dict(status=out["status"], witnesses_checked=len(reports), totals=totals,
        minimal_verified_examples=examples, seconds=out["seconds"]), indent=2))


if __name__ == "__main__":
    main()
