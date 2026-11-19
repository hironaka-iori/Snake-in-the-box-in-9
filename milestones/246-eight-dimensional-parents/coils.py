"""Replay the five single-collision placements and identify their induced cycles."""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent


def steps(path):
    return [(a ^ b).bit_length() - 1 for a, b in zip(path, path[1:])]


def shape(path):
    def rename(word):
        names = {}
        return tuple(names.setdefault(axis, len(names)) for axis in word)
    word = steps(path)
    return min(rename(word), rename(reversed(word)))


def apply_axes(vertex, image):
    return sum(1 << dest for source, dest in enumerate(image) if vertex & (1 << source))


def verify_cycle(cycle):
    n = len(cycle)
    assert len(set(cycle)) == n and all(0 <= x < 512 for x in cycle)
    for (i, u), (j, v) in combinations(enumerate(cycle), 2):
        assert ((u ^ v).bit_count() == 1) == (j-i in (1, n-1))
    return n * (n-1) // 2


def coil_isometry(cycle, published):
    n = len(cycle)
    if n != len(published):
        return None
    source_steps = steps(cycle + cycle[:1])
    for direction in (1, -1):
        for offset in range(n):
            ordered = [published[(offset + direction*j) % n] for j in range(n)]
            image = {}
            for a, b in zip(source_steps, steps(ordered + ordered[:1])):
                if a in image and image[a] != b:
                    break
                image[a] = b
            else:
                if len(image) != 9 or len(set(image.values())) != 9:
                    continue
                axes = [image[i] for i in range(9)]
                translation = apply_axes(cycle[0], axes) ^ ordered[0]
                assert all((apply_axes(v, axes) ^ translation) == target
                           for v, target in zip(cycle, ordered))
                return dict(source_axis_to_published_axis=axes, xor_after_permutation=translation,
                            published_start_index=offset, published_index_step=direction,
                            vertex_images_verified=n)
    return None


def main():
    files = [HERE / "placements.json", HERE / "donors.json",
             HERE.parents[1] / "work/bank9.json", HERE.parent / "243-coil-opening/coil9.json"]
    placements, donors, bank, coil_data = [json.loads(p.read_bytes()) for p in files]
    paths = [d["path"] for d in donors["shapes"]]
    published, = coil_data["q9_rows"]
    published = published["vertices"]
    assert len(published) == 192
    coil_pairs = verify_cycle(published)
    bank_shapes = [shape(entry["vertex_sequence"]) for entry in bank]
    records = []
    for r in placements["records"]:
        if r["scope"] != "target_192" or r["min_extra_overlap"] != 1:
            continue
        assert r["lengths"] == [96, 95] and r["minimizing_placements"] == 1
        first = paths[r["long_donor"]][::-1] if r["long_endpoint"] else paths[r["long_donor"]]
        second = paths[r["short_donor"]][::-1] if r["short_endpoint"] else paths[r["short_donor"]]
        first = [apply_axes(v ^ first[0], r["axis_image"]) for v in first]
        second = [v ^ second[0] for v in second]
        walk = first[::-1] + [v | 256 for v in second]
        assert len(walk) == len(set(walk)) == 193
        assert all(0 <= x < 512 for x in walk)
        assert all((u ^ v).bit_count() == 1 for u, v in zip(walk, walk[1:]))
        chord, = [(i, j) for (i, u), (j, v) in combinations(enumerate(walk), 2)
                  if j > i + 1 and (u ^ v).bit_count() == 1]
        start, end = chord
        assert end == 192 and (walk[start] ^ walk[end]) == 256
        cycle = walk[start:end+1]
        checked = verify_cycle(cycle)
        isometry = coil_isometry(cycle, published)
        assert (isometry is not None) == (len(cycle) == 192)
        prefix_shape = shape(walk[:-1])
        matched = [i for i, key in enumerate(bank_shapes) if key == prefix_shape]
        assert matched
        records.append(dict(long_donor=r["long_donor"], short_donor=r["short_donor"],
                            unique_minimizing_placement=True, walk=walk,
                            unique_chord_zero_based=[start, end],
                            chord_vertices=[walk[start], walk[end]],
                            walk_pairs_checked=193*192//2, induced_cycle_length=len(cycle),
                            cycle_pairs_checked=checked, prefix_191_bank_indices=matched,
                            isometry_to_published_coil=isometry))
    assert sorted((r["long_donor"], r["induced_cycle_length"]) for r in records) == [
        (30, 180), (49, 186), (59, 186), (69, 192), (73, 192)]
    result = dict(inputs_sha256={p.name: sha256(p.read_bytes()).hexdigest() for p in files},
                  index_convention="All indices are zero-based. The induced cycle is the closed walk interval between the two chord indices.",
                  isometry_convention="Permute source axes, then XOR the recorded translation. Source cycle vertex j maps to published vertex (start + step*j) modulo 192.",
                  published_coil_pairs_checked=coil_pairs, records=records)
    (HERE / "coils.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print([(r["long_donor"], r["unique_chord_zero_based"], r["induced_cycle_length"]) for r in records])


if __name__ == "__main__":
    main()
