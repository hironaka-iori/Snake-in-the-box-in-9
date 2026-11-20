"""Exact longest rooted partner among all contiguous segments of the donor bank."""
from bisect import bisect_left
from hashlib import sha256
from itertools import islice, permutations
import json
from math import factorial
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
DONORS = HERE.parent / "246-eight-dimensional-parents" / "donors.json"
CENSUS = HERE / "census-72.json"
PERMUTATIONS = factorial(8)
ALL_MAPS = (1 << PERMUTATIONS) - 1


def check_path(path, dimension):
    if not path or len(set(path)) != len(path) or not all(0 <= v < 1 << dimension for v in path):
        raise ValueError("Invalid cube vertices")
    for j, v in enumerate(path):
        for i in range(j):
            if ((path[i] ^ v).bit_count() == 1) != (i + 1 == j):
                raise ValueError(("Induced path adjacency", dimension, i, j))
    return len(path) * (len(path) - 1) // 2


def donor_suffixes(donors):
    # Every directed segment is the prefix of a suffix in one of the two orders.
    representatives = {}
    for donor, path in enumerate(donors):
        check_path(path, 8)
        steps = bytes((u ^ v).bit_length() - 1 for u, v in zip(path, path[1:]))
        for direction, sequence in ((1, steps), (-1, steps[::-1])):
            for start in range(len(sequence)):
                suffix = sequence[start:]
                order = bytes(dict.fromkeys(suffix))
                word = suffix.translate(bytes.maketrans(order, bytes(range(len(order)))))
                origin = start if direction == 1 else len(steps) - start
                representatives.setdefault(word, (donor, origin, direction))
    return sorted(representatives), representatives


def permutation_images():
    """Image of each cube vertex under each axis map, in lexicographic order."""
    flips = [bytes(v ^ (1 << axis) for v in range(256)) for axis in range(8)]
    for axes in permutations(range(8)):
        images = bytes([0])
        for axis in axes:
            images += images.translate(flips[axis])
        yield images


def allowed_maps(parent, images):
    # Bit k at vertex v is set iff map k places v outside the forbidden set.
    forbidden = set(parent[1:])
    flags = [bytes(0 if v in forbidden else 1 << bit for v in range(256)) for bit in range(8)]
    rows = bytearray()
    for group in range(0, PERMUTATIONS, 8):
        row = 0
        for bit in range(8):
            row |= int.from_bytes(images[group + bit].translate(flags[bit]), "little")
        rows.extend(row.to_bytes(256, "little"))
    allowed = [int.from_bytes(rows[v::256], "little") for v in range(256)]
    for v, maps in enumerate(allowed):
        weight = v.bit_count()
        sites = sum(x.bit_count() == weight and x not in forbidden for x in range(256))
        if maps.bit_count() != sites * factorial(weight) * factorial(8 - weight):
            raise ValueError(("Wrong permutation count in weight class", v))
    return allowed


def longest(words, allowed):
    # Reuse live map sets on common prefixes. A forbidden prefix eliminates
    # its entire interval of directed suffixes in the sorted catalogue.
    states = [(0, ALL_MAPS)]
    previous = b""
    best = (0, words[0], 0)
    index = 0
    while index < len(words):
        word = words[index]
        shared = 0
        while shared < min(len(word), len(states) - 1) and word[shared] == previous[shared]:
            shared += 1
        del states[shared + 1:]
        vertex, maps = states[-1]
        for depth in range(shared, len(word)):
            vertex ^= 1 << word[depth]
            maps &= allowed[vertex]
            if not maps:
                index = bisect_left(words, word[:depth + 1] + b"\xff", lo=index + 1)
                break
            states.append((vertex, maps))
            if depth + 1 > best[0]:
                best = (depth + 1, word, (maps & -maps).bit_length() - 1)
        else:
            index += 1
        previous = word
    return best


def exclude_next(donors, words, allowed, length):
    # Fresh fixed-length pass without lexicographic interval pruning. The
    # vertices can be examined in reverse because only their intersection matters.
    prefixes = sorted({word[:length] for word in words if len(word) >= length})
    digest = sha256()
    for word in prefixes:
        digest.update(word)
        vertices = []
        vertex = 0
        for axis in word:
            vertex ^= 1 << axis
            vertices.append(vertex)
        maps = ALL_MAPS
        for vertex in reversed(vertices):
            maps &= allowed[vertex]
            if not maps:
                break
        if maps:
            raise ValueError(("Longer partner found in exhaustive next-length pass", word.hex()))
    return dict(partner_edges=length, oriented_occurrences=2 * sum(max(0, len(p) - length) for p in donors),
                distinct_rooted_transition_words=len(prefixes), axis_maps_per_word=PERMUTATIONS,
                sorted_concatenated_transition_bytes_sha256=digest.hexdigest(), compatible_placements=0)


def make_witness(donors, descriptor, best, parent):
    length, word, rank = best
    donor, origin, direction = descriptor
    segment = [donors[donor][origin + direction * i] for i in range(length + 1)]
    axes = next(islice(permutations(range(8)), rank, None))
    raw_steps = [(a ^ b).bit_length() - 1 for a, b in zip(segment, segment[1:])]
    first_axes = list(dict.fromkeys(raw_steps))
    first_axes.extend(i for i in range(8) if i not in first_axes)
    if bytes(first_axes.index(i) for i in raw_steps) != word[:length]:
        raise ValueError("Donor indices disagree with canonical prefix")
    donor_image = [axes[first_axes.index(i)] for i in range(8)]
    partner = [sum(1 << donor_image[i] for i in range(8) if (v ^ segment[0]) & (1 << i)) for v in segment]
    if set(parent) & set(partner) != {0}:
        raise ValueError("Projected arms have an extra intersection")
    joined = parent[::-1] + [256 + v for v in partner]
    pairs = dict(parent=check_path(parent, 8), partner=check_path(partner, 8), joined=check_path(joined, 9))
    return dict(donor_index=donor, donor_start=origin, donor_step=direction, donor_axes_image=donor_image,
                donor_segment=segment, parent=parent, partner=partner, joined=joined, partner_edges=length,
                joined_edges=len(joined) - 1, all_pairs=pairs)


def main():
    donors = [row["path"] for row in json.loads(DONORS.read_bytes())["shapes"]]
    shapes = json.loads(CENSUS.read_bytes())["new_shapes"]
    if len(sys.argv) == 1:
        cases = [(index, end) for index in range(len(shapes)) for end in range(2)]
    elif len(sys.argv) == 3:
        index, end = map(int, sys.argv[1:])
        if index not in range(len(shapes)) or end not in (0, 1):
            raise ValueError("Shape index or endpoint outside census")
        cases = [(index, end)]
    else:
        raise SystemExit("Usage: bank_capacity.py [SHAPE_INDEX END]")
    words, representatives = donor_suffixes(donors)
    images = list(permutation_images())
    pins = {p.name: sha256(p.read_bytes()).hexdigest() for p in (DONORS, CENSUS, Path(__file__))}
    for index, end in cases:
        row = shapes[index]
        order = row["path"] if end == 0 else row["path"][::-1]
        parent = [v ^ order[0] for v in order]
        allowed = allowed_maps(parent, images)
        best = longest(words, allowed)
        witness = make_witness(donors, representatives[best[1]], best, parent)
        exclusion = exclude_next(donors, words, allowed, best[0] + 1)
        result = dict(inputs=pins, id=row["id"], shape_index=index, end=end, original_root=order[0],
                      donor_count=len(donors), distinct_directed_suffixes=len(words),
                      witness=witness, next_length_exclusion=exclusion)
        destination = HERE / f"bank-capacity-{index}-{end}.json"
        temporary = destination.with_suffix(".tmp")
        temporary.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
        temporary.replace(destination)
        print(index, end, "longest partner", best[0], "join", witness["joined_edges"], flush=True)


if __name__ == "__main__":
    main()
