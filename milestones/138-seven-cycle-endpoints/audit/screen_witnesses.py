"""Independently validate saved actual snakes and screen the saved seven-cycle.

This script imports no solver, Lean driver, or full-graph evaluator.
"""
from collections import Counter
from pathlib import Path
import hashlib
import itertools
import json
import re
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PAIRS = list(itertools.combinations(range(9), 2))


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canon(word):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in word)


def validate(vertices):
    assert all(type(v) is int and 0 <= v < 512 for v in vertices)
    assert len(set(vertices)) == len(vertices)
    checked = 0
    for i, u in enumerate(vertices):
        for j in range(i + 1, len(vertices)):
            assert ((u ^ vertices[j]).bit_count() == 1) == (j == i + 1)
            checked += 1
    directions = [(a ^ b).bit_length() - 1 for a, b in zip(vertices, vertices[1:])]
    selected = set(vertices)
    alpha = {}
    for k in range(1, len(vertices) - 1):
        incident = {directions[k - 1], directions[k]}
        assert len(incident) == 2
        allowed = [(a, b) for a, b in PAIRS if a not in incident and b not in incident]
        assert len(allowed) == 21
        count21 = sum(vertices[k] ^ (1 << a) ^ (1 << b) not in selected for a, b in allowed)
        count36 = sum(
            vertices[k] ^ (1 << a) not in selected
            and vertices[k] ^ (1 << b) not in selected
            and vertices[k] ^ (1 << a) ^ (1 << b) not in selected
            for a, b in PAIRS
        )
        assert count21 == count36
        alpha[k] = count21
    return directions, alpha, checked


def window_record(vertices, directions, alpha, start, width, offsets, reverse):
    m = len(vertices) - 1
    centre_indices = [start + x for x in offsets]
    return dict(
        orientation="reversed" if reverse else "forward",
        oriented_start=start,
        original_vertex_indices=[m - (start + j) if reverse else start + j for j in range(width + 1)],
        vertices=vertices[start:start + width + 1],
        directions=directions[start:start + width],
        canonical_directions=list(canon(directions[start:start + width])),
        centre_offsets=offsets,
        counts=[alpha[k] for k in centre_indices],
        clipped_counts=[min(6, alpha[k]) for k in centre_indices],
        endpoints=[vertices[0], vertices[-1]],
        centre_endpoint_distances=[
            [(vertices[k] ^ vertices[0]).bit_count(), (vertices[k] ^ vertices[-1]).bit_count()]
            for k in centre_indices
        ],
    )


def screen(vertices, targets):
    directions, alpha, checked = validate(vertices)
    m = len(vertices) - 1
    stats = [dict(row=i, full_shape=0, full_count_shape=0, suffix_shape=0, suffix_count_shape=0)
             for i in range(len(targets))]
    matches, triples, near_twos = [], [], []
    for reverse in (False, True):
        v = list(reversed(vertices)) if reverse else vertices
        d = list(reversed(directions)) if reverse else directions
        a = {k: alpha[m - k] for k in range(1, m)} if reverse else alpha
        for width, offsets, kind in [(9, list(range(3, 9)), "full"),
                                     (7, list(range(1, 7)), "suffix")]:
            for start in range(m - width + 1):
                shape = canon(d[start:start + width])
                counts = [a[start + offset] for offset in offsets]
                clipped = [min(6, x) for x in counts]
                for row, target in enumerate(targets):
                    wanted_word = target["directions"] if width == 9 else target["directions"][2:]
                    if shape != canon(wanted_word):
                        continue
                    stats[row][kind + "_shape"] += 1
                    if clipped != target["counts"]:
                        continue
                    stats[row][kind + "_count_shape"] += 1
                    matches.append(dict(cycle_row=row, window_kind=kind,
                        **window_record(v, d, a, start, width, offsets, reverse)))
        # This property is reversal invariant, so each physical four-edge window is recorded once.
        if not reverse:
            for start in range(m - 3):
                if len(set(d[start:start + 4])) == 4 and [a[start + j] for j in (1, 2, 3)] == [3, 3, 3]:
                    triples.append(window_record(v, d, a, start, 4, [1, 2, 3], False))
        # The cycle has a 5,2,>=6,>=6 count neighbourhood. Test both orientations.
        for centre in range(2, m - 2):
            if a[centre - 1] == 5 and a[centre] == 2 and a[centre + 1] >= 6 and a[centre + 2] >= 6:
                near_twos.append(dict(alpha2_centre_offset=2,
                    **window_record(v, d, a, centre - 2, 5, [1, 2, 3, 4], reverse)))
    alpha2 = [k for k, value in alpha.items() if value == 2]
    return dict(edges=m, parity=m % 2, vertices=len(vertices), pairs_checked=checked,
        induced_and_distinct=True, internal_counts_crosschecked=len(alpha),
        alpha_histogram=dict(sorted(Counter(alpha.values()).items())),
        full_windows_per_orientation=max(0, m - 8), suffix_windows_per_orientation=max(0, m - 6),
        cycle_row_statistics=stats, qualifying_cycle_windows=matches,
        triple333_four_distinct_windows=triples, alpha2_count=len(alpha2),
        alpha2_adjacent_clipped_histogram=dict(sorted(Counter(
            str((min(6, alpha[k - 1]) if k - 1 in alpha else None,
                 min(6, alpha[k + 1]) if k + 1 in alpha else None)) for k in alpha2).items())),
        alpha2_neighbourhood_5_2_6plus_6plus=near_twos)


def main():
    started = time.monotonic()
    pins = {}

    def read(rel):
        raw = (ROOT / rel).read_bytes()
        pins[rel] = sha(raw)
        return raw.decode("utf-8-sig")

    cycle_rel = "milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json"
    cycle_data = json.loads(read(cycle_rel))
    profile = next(p for p in cycle_data["profiles"] if p["profile"] == "conditional_floor18")
    targets = profile["cycle"]
    assert len(targets) == 7
    assert all(len(t["directions"]) == 9 and len(t["counts"]) == 6 for t in targets)
    assert all(1 <= x <= 6 for t in targets for x in t["counts"])
    # Check the saved count codes independently, preserving left-to-right chronology.
    for t in targets:
        assert [t["count_code"] // 6**j % 6 + 1 for j in range(5, -1, -1)] == t["counts"]
    semantics_sources = [
        "milestones/131-odd-pair-six-count/audit/screen_endpoint9.py",
        "milestones/131-odd-pair-six-count/scripts/evaluate_graph.py",
        "milestones/59-extended-share-window/scripts/extend.py",
        "milestones/59-extended-share-window/README.md",
        "work/final_lean/LocalWindowBridge.lean",
        "work/final_lean/LocalWindowModel.lean",
    ]
    texts = {rel: read(rel) for rel in semantics_sources}
    assert "word[2:]" in texts[semantics_sources[1]]
    assert "word[s+2:s+8]" in texts[semantics_sources[1]]
    assert "five = values[:,s:s+5]" in texts[semantics_sources[1]]
    assert "positions 3,...,8" in texts[semantics_sources[3]]
    candidates = []
    for rel, name in [("work/final_lean/Snake9.lean", "witnessValues"),
                      ("work/spectral/stronger/EndpointFourWitness.lean", "values")]:
        source = read(rel)
        body = re.search(r"def " + name + r" : Array Nat := #\[([^]]+)\]", source).group(1)
        candidates.append((rel, name, [int(x) for x in body.split(",")]))
    bank_rel = "work/bank9.json"
    for i, entry in enumerate(json.loads(read(bank_rel))):
        candidates.append((bank_rel, i, entry["vertex_sequence"]))
    for folder in ["probe-endpoint18", "probe-balanced"]:
        rel = f"milestones/133-endpoint-occurrences/work/{folder}/actual-path.json"
        candidates.append((rel, "ordered_path", json.loads(read(rel))["ordered_path"]))
    grouped = {}
    for rel, key, vertices in candidates:
        grouped.setdefault(tuple(vertices), []).append(dict(source=rel, source_entry=key,
            source_sha256=pins[rel]))
    rows = []
    for vertices, aliases in grouped.items():
        row = screen(list(vertices), targets)
        row.update(source_entries=aliases, vertex_sequence_sha256=sha(
            json.dumps(vertices, separators=(",", ":")).encode("ascii")))
        rows.append(row)
    totals = dict(source_entries=len(candidates), distinct_vertex_sequences=len(rows),
        unordered_vertex_pairs_checked=sum(r["pairs_checked"] for r in rows),
        internal_counts_crosschecked=sum(r["internal_counts_crosschecked"] for r in rows),
        full_shape_matches=sum(s["full_shape"] for r in rows for s in r["cycle_row_statistics"]),
        full_count_shape_matches=sum(s["full_count_shape"] for r in rows for s in r["cycle_row_statistics"]),
        suffix_shape_matches=sum(s["suffix_shape"] for r in rows for s in r["cycle_row_statistics"]),
        suffix_count_shape_matches=sum(s["suffix_count_shape"] for r in rows for s in r["cycle_row_statistics"]),
        triple333_four_distinct_windows=sum(len(r["triple333_four_distinct_windows"]) for r in rows),
        alpha2_centres=sum(r["alpha2_count"] for r in rows),
        alpha2_neighbourhood_5_2_6plus_6plus=sum(len(r["alpha2_neighbourhood_5_2_6plus_6plus"]) for r in rows))
    per_target = [dict(row=i, directions=t["directions"], suffix=t["directions"][2:], counts=t["counts"],
        **{key: sum(r["cycle_row_statistics"][i][key] for r in rows)
           for key in ["full_shape", "full_count_shape", "suffix_shape", "suffix_count_shape"]})
        for i, t in enumerate(targets)]
    out = dict(status="FINITE_ACTUAL_WITNESS_SCREEN_COMPLETE", profile="conditional_floor18",
        saved_cycle_mean=profile["mean"], cycle=per_target, totals=totals,
        count_semantics="Nine transitions: counts at vertex offsets 3..8. Seven-transition suffix word[2:]: counts at offsets 1..6. Symbol 6 means actual count >=6.",
        orientation_semantics="Both entire actual paths are oriented independently. On reversal, full-nine counts are recomputed at reversed offsets 3..8, not obtained by reversing the original six counts. Suffix counts reverse in the usual way.",
        count_method="All 21 free-coordinate opposite corners, independently crosschecked against all 36 singleton-square predicates at every internal vertex.",
        full_pattern_screen_vacuous=totals["full_count_shape_matches"] == 0,
        suffix_pattern_screen_vacuous=totals["suffix_count_shape_matches"] == 0,
        witnesses=rows, source_files_sha256=pins, script_sha256=sha(Path(__file__).read_bytes()),
        seconds=time.monotonic() - started,
        scope="Existing independently validated actual snakes only. No SAT, Lean, or full-graph run. Matching local windows do not realize the whole cycle; no matches do not exclude them universally.")
    destination = HERE / "data/witness-screen.json"
    destination.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    table = "\n".join(f"| {r['row']} | {''.join(map(str,r['directions']))} | {r['counts']} | {r['full_shape']} / {r['full_count_shape']} | {r['suffix_shape']} / {r['suffix_count_shape']} |"
                      for r in per_target)
    report = f"""# Saved actual witnesses and the seven-cycle

The screen completed on {totals['source_entries']} source entries, representing {totals['distinct_vertex_sequences']} distinct exact vertex sequences. It found {totals['full_count_shape_matches']} full nine-direction count-and-shape matches and {totals['suffix_count_shape_matches']} seven-direction suffix count-and-shape matches to the saved conditional-floor18 seven-cycle.

| Row | Nine directions | Count symbols | Full: shape / count-and-shape | Suffix: shape / count-and-shape |
| --- | --- | --- | --- | --- |
{table}

Counts in a nine-transition row belong to vertex positions 3 through 8. The seven-transition suffix starts at direction position 2, so its six counts occupy positions 1 through 6. This alignment was checked against the saved generator, its five-count slice offsets, and the model description. Symbol 6 means at least 6. Count-code decoding was independently checked for all seven rows.

Both path orientations were tested after coordinate canonicalization. For a full nine-direction window, reversing the path changes which six centres occupy positions 3 through 8; the script recomputes those positions instead of merely reversing the original count list. Shape-only hits do not satisfy the count restrictions.

The additional screens found {totals['triple333_four_distinct_windows']} four-distinct-transition windows with three consecutive counts 3,3,3; {totals['alpha2_centres']} centres with count 2; and {totals['alpha2_neighbourhood_5_2_6plus_6plus']} oriented neighbourhoods with counts 5,2,at-least-6,at-least-6. These are subsidiary local tests, not replacements for a complete cycle match.

Every distinct sequence was checked for membership in Q9, distinct vertices, and adjacency exactly at consecutive indices. This checked {totals['unordered_vertex_pairs_checked']} unordered vertex pairs. All {totals['internal_counts_crosschecked']} internal counts were computed in two independent ways: the 21 allowed opposite corners and the 36 singleton-square predicates. Identical source sequences were grouped, with every source entry and raw-file hash retained.

The JSON retains all qualifying windows, actual vertices, exact counts, orientations, global endpoints and centre-to-endpoint distances, together with per-witness summary counts and source hashes. It also contains the two actual odd witnesses from milestone133. {'The full count-and-shape screen is vacuous: none of these witnesses supplies a qualifying full pattern.' if out['full_pattern_screen_vacuous'] else 'The full matches demonstrate only local realizability in the saved witnesses.'} {'The suffix count-and-shape screen is also vacuous.' if out['suffix_pattern_screen_vacuous'] else 'The suffix matches demonstrate only local realizability in the saved witnesses.'}

No universal endpoint implication, local exclusion, periodic-cycle realization, or global snake-length bound follows from this finite screen. No solver, Lean process, or full-graph evaluator was run.
"""
    (HERE / "audit/witness-screen.md").write_text(report, encoding="utf-8")
    print(json.dumps(dict(status=out["status"], totals=totals, seconds=out["seconds"]), indent=2))


if __name__ == "__main__":
    main()
