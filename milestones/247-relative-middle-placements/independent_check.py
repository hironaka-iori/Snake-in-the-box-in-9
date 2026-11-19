"""Count forbidden translations directly from pairs of Q7 middle vertices."""
from collections import Counter
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "246-eight-dimensional-parents"


def relabel(vertex, axes):
    return sum(1 << axes[i] for i in range(7) if vertex & (1 << i))


def check_path(path):
    assert len(path) == len(set(path)) == 48
    assert all(0 <= x < 128 for x in path)
    for i, x in enumerate(path):
        for j in range(i + 1, len(path)):
            assert ((x ^ path[j]).bit_count() == 1) == (j == i + 1)


def main():
    inputs = [PREVIOUS / "middle.json", HERE / "orbit.json"]
    middle, first_survey = [json.loads(p.read_bytes()) for p in inputs]
    path, reference = middle["layouts"][0]["middles"]
    check_path(path)
    check_path(reference)
    assert path == first_survey["first"] and reference == first_survey["reference"]
    assert sum(x.bit_count() % 2 == 0 for x in path) == 24
    hist = Counter()
    coverage = Counter()
    unique = []
    stabilizers = []
    rows = []
    for axes in permutations(range(7)):
        source = [relabel(x, axes) for x in path]
        counts = [0] * 128
        # For fixed axes and each intersecting pair, exactly t = x XOR y
        # puts y onto x. Since both path lists have distinct vertices, this
        # counts one pair per intersection vertex for a specified translation.
        for y in source:
            for x in path:
                counts[x ^ y] += 1
        assert sum(counts) == 48 * 48
        assert sum(counts[t] for t in range(128) if t.bit_count() % 2 == 0) == 2 * 24**2
        hist.update(counts)
        covered = 128 - counts.count(0)
        coverage[covered] += 1
        rows.append(dict(axes="".join(map(str, axes)), covered_translations=covered,
                         multiplicities_by_translation_hex=bytes(counts).hex()))
        for t, common in enumerate(counts):
            if common not in (0, 48):
                continue
            image = [v ^ t for v in source]
            assert len(set(path) & set(image)) == common
            record = dict(axes=list(axes), translation=t, path=image)
            (unique if common == 0 else stabilizers).append(record)

    assert len(rows) == 5040 and sum(hist.values()) == 645120
    assert hist == {int(k): v for k, v in first_survey["intersection_histogram"].items()}
    assert unique == first_survey["disjoint"] and stabilizers == first_survey["stabilizers"]
    assert len(unique) == len(stabilizers) == 1
    assert stabilizers[0]["axes"] == list(range(7)) and stabilizers[0]["translation"] == 0
    winner = unique[0]
    assert winner["path"] == reference or winner["path"] == reference[::-1]
    image = [relabel(x, winner["axes"]) ^ winner["translation"] for x in range(128)]
    assert all(image[image[x]] == x and image[x] != x for x in range(128))
    assert all((x ^ image[x]).bit_count() % 2 == 1 for x in range(128))
    cycles = [(x, y) for x, y in enumerate(image) if x < y]
    membership = set(path)
    occupancy = Counter(int(x in membership) + int(y in membership) for x, y in cycles)
    assert occupancy == {0: 16, 1: 48} and len(cycles) == 64

    result = dict(inputs_sha256={p.name: sha256(p.read_bytes()).hexdigest() for p in inputs},
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  comparison="fix the first path; range over every axis permutation then XOR translation of its copy",
                  row_encoding="byte t of the hexadecimal data is the number of intersecting vertex pairs at translation t",
                  per_permutation=rows, covered_translation_histogram=coverage,
                  intersection_histogram=hist, disjoint=winner, stabilizer=stabilizers[0],
                  reference_reversed=(winner["path"] == reference[::-1]),
                  path_parities=[24, 24], intersection_sum_per_translation_parity_per_axes=[1152, 1152],
                  exceptional_translation_weight=winner["translation"].bit_count(),
                  exceptional_map_displacement_histogram=Counter((v ^ w).bit_count() for v, w in enumerate(image)),
                  exceptional_involution_pair_occupancy=occupancy,
                  reversed_order_note="Reversing a path leaves the vertex set unchanged. The sole set stabilizer is the identity, so no additional self-reversal map is suppressed.")
    (HERE / "independent-check.json").write_text(json.dumps(result, separators=(",", ":")) + "\n",
                                                 encoding="utf-8", newline="\n")
    print("XOR difference counts:", len(rows), "permutations;", coverage, "covered translations")
    print("Disjoint map:", winner["axes"], winner["translation"], "involution pairs:", occupancy)


if __name__ == "__main__":
    main()
