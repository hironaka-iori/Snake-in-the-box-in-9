"""Verify the projected arm classes, their joins, and their lower-dimensional cuts."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def verify_path(vertices, dimension):
    assert len(vertices) == len(set(vertices))
    assert all(0 <= v < 1 << dimension for v in vertices)
    for (i, u), (j, v) in combinations(enumerate(vertices), 2):
        assert ((u ^ v).bit_count() == 1) == (j == i + 1)
    return len(vertices) * (len(vertices) - 1) // 2


def word(path):
    return [(a ^ b).bit_length() - 1 for a, b in zip(path, path[1:])]


def rename(steps):
    seen = {}
    return tuple(seen.setdefault(s, len(seen)) for s in steps)


def shape(path):
    steps = word(path)
    return min(rename(steps), rename(reversed(steps)))


def extensions(path):
    choices = []
    for ordered in (path, path[::-1]):
        endpoint, *others = ordered
        possible = []
        for i in range(8):
            v = endpoint ^ (1 << i)
            if all((v ^ u).bit_count() >= 2 for u in others):
                possible.append(v)
        choices.append(possible)
    return choices


def profile(path):
    counts = Counter(word(path))
    return dict(endpoints=[path[0], path[-1]],
                endpoint_distance=(path[0] ^ path[-1]).bit_count(),
                crossing_counts=[counts[i] for i in range(8)],
                extensions_at_ordered_ends=extensions(path))


def least_cuts(path):
    steps = word(path)
    minimum = min(steps.count(i) for i in range(8))
    cuts = []
    for i in range(8):
        if steps.count(i) != minimum:
            continue
        indices = [j for j, s in enumerate(steps) if s == i]
        boundaries = [-1, *indices, len(path) - 1]
        mask = (1 << i) - 1
        pieces = []
        rebuilt = []
        for a, b in zip(boundaries, boundaries[1:]):
            local = path[a + 1:b + 1]
            layer = (local[0] >> i) & 1
            assert all(((v >> i) & 1) == layer for v in local)
            projected = [(v & mask) | ((v >> (i + 1)) << i) for v in local]
            verify_path(projected, 7)
            pieces.append(projected)
            rebuilt.extend((v & mask) | (layer << i) | ((v >> i) << (i + 1))
                           for v in projected)
        assert rebuilt == path
        pairs = verify_path(rebuilt, 8)
        cuts.append(dict(axis=i, crossing_edges_zero_based=indices,
                         component_lengths=[len(p) - 1 for p in pieces],
                         q7_paths=pieces, reconstructed_q8_pairs_checked=pairs))
    return cuts


def main():
    source = HERE / "comparison.json"
    comparison = json.loads(source.read_bytes())
    examples = comparison["examples"]
    optimal = examples["optimal_98"]["path"]
    verify_path(optimal, 8)
    controls = {}
    windows = set()
    for i, name in enumerate(("first_97_vertices", "middle_97_vertices", "last_97_vertices")):
        path = examples[name]["path"]
        assert path == optimal[i:i + 97]
        verify_path(path, 8)
        windows.add(shape(path))
        controls[name] = dict(**profile(path), original_start_index=i,
                              original_deleted_ends=[i, 2 - i])

    classes = {"long": {}, "short": {}}
    representatives = {"long": {}, "short": {}}
    cells = {}
    records = []
    for row in sorted(comparison["one_crossing_pairs"], key=lambda r: r["seed"]):
        seed = row["seed"]
        first, second = row["long"], row["short"]
        assert len(first) == 97 and len(second) == 95
        assert first[0] == second[0] == 0
        assert set(first).intersection(second) == {0}
        lift = first[::-1] + [v | 256 for v in second]
        pairs = [verify_path(first, 8), verify_path(second, 8), verify_path(lift, 9)]
        ids = []
        for side, arm in (("long", first), ("short", second)):
            key = shape(arm)
            if key not in classes[side]:
                classes[side][key] = seed
                representatives[side][seed] = dict(**profile(arm), least_cuts=least_cuts(arm))
            ids.append(classes[side][key])
        assert tuple(ids) not in cells
        cells[tuple(ids)] = seed
        root_options, tip_options = extensions(second)
        blockers = [dict(candidate=v, long_index_from_join=first.index(v) if v in first else None)
                    for v in tip_options]
        records.append(dict(seed=seed, q9_crossing_coordinate=row["axis"],
                            long_class=ids[0], short_class=ids[1], pairs_checked=pairs,
                            shared_projection=0, long_end_extensions=extensions(first),
                            short_root_extensions=root_options, short_tip_extensions=blockers))

    long_ids = sorted(representatives["long"])
    short_ids = sorted(representatives["short"])
    assert len(long_ids) == len(short_ids) == 5
    assert set(cells) == {(a, b) for a in long_ids for b in short_ids}
    assert windows.isdisjoint(classes["long"])
    middle_source = HERE.parent / "188-dimensional-constructions/data/middle-ancestry.json"
    middle_rows = [row for row in json.loads(middle_source.read_bytes())["rows"]
                   if row["middle_length"] == 95]
    bank_middle = middle_rows[0]["middle_vertices"]
    assert len(middle_rows) == 84
    assert all(shape(row["middle_vertices"]) == shape(bank_middle) for row in middle_rows)
    verify_path(bank_middle, 8)
    central_cuts = least_cuts(bank_middle)
    common = {shape(cut["q7_paths"][1]) for cut in central_cuts
              if len(cut["q7_paths"]) == 3 and len(cut["q7_paths"][1]) == 48}
    assert len(common) == 1
    middle_matches = {side: [seed for seed, entry in representatives[side].items()
                             if any(len(cut["q7_paths"]) == 3
                                    and shape(cut["q7_paths"][1]) in common
                                    for cut in entry["least_cuts"])]
                      for side in representatives}
    assert middle_matches == {"long": [0, 3, 4, 5, 8], "short": [0, 1, 2, 7]}
    result = dict(comparison_sha256=sha256(source.read_bytes()).hexdigest(),
                  middle_ancestry_sha256=sha256(middle_source.read_bytes()).hexdigest(),
                  class_labels="First zero-based bank ID of each isometry class, allowing reversal.",
                  pair_check_order=["96 arm", "94 arm", "191-edge two-layer join"],
                  long_class_ids=long_ids, short_class_ids=short_ids,
                  seed_ids_by_long_row_short_column=[[cells[(a, b)] for b in short_ids]
                                                     for a in long_ids],
                  representatives=representatives, pair_receipts=records,
                  optimal_98=dict(**profile(optimal), least_cuts=least_cuts(optimal)),
                  contiguous_controls=controls, control_matches_any_published_long_arm=False,
                  dominant_95_middle=dict(bank_seed=middle_rows[0]["bank_index"],
                                          occurrences=len(middle_rows), least_cuts=central_cuts),
                  common_47_q7_canonical_word=list(next(iter(common))),
                  representatives_sharing_95_middle_q7_piece=middle_matches)
    (HERE / "arm-structure.json").write_text(json.dumps(result, indent=2) + "\n",
                                             encoding="utf-8")


if __name__ == "__main__":
    main()
