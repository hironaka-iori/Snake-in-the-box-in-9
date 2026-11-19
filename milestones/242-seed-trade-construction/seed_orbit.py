"""Compare the complete eight-count orbit with both colours of every saved Q9 path."""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BANK = ROOT / "work/bank9.json"
WITNESS = HERE.parent / "241-exact-count-distance/witness.json"


def bits(vertices):
    return sum(1 << v for v in vertices)


def seed_classes():
    classes = [{}, {}]
    for i, row in enumerate(json.loads(BANK.read_bytes())):
        path = row["vertex_sequence"]
        if len(path) != 192 or len(set(path)) != 192 or any(not 0 <= v < 512 for v in path):
            raise ValueError(("seed size", i))
        for j, v in enumerate(path):
            for k in range(j):
                if ((v ^ path[k]).bit_count() == 1) != (j == k + 1):
                    raise ValueError(("seed adjacency", i, k, j))
        for parity, side in enumerate(classes):
            mask = bits(v for v in path if v.bit_count() % 2 == parity)
            if mask.bit_count() != 96:
                raise ValueError(("seed colour size", i))
            side.setdefault(mask, []).append(i)
    return classes


def partitions():
    coords = set(range(9))
    for four in combinations(range(9), 4):
        rest = coords.difference(four)
        for single in sorted(rest):
            paired = rest - {single}
            for first in combinations(sorted(paired), 2):
                second = tuple(sorted(paired.difference(first)))
                if first < second:
                    yield (four, first, second, (single,))


def placements(blocks, witness):
    permutation = [j for block in blocks for j in block]
    def permute(x):
        return sum(((x >> i) & 1) << j for i, j in enumerate(permutation))
    add = list(map(permute, witness["positive_selection"]))
    remove = list(map(permute, witness["negative_selection"]))
    pivots = sum(1 << block[0] for block in blocks[:3])
    for t in range(512):
        if not t & pivots:
            yield t, bits(x ^ t for x in remove), bits(x ^ t for x in add)


def main():
    witness = json.loads(WITNESS.read_bytes())
    classes = seed_classes()
    records = [[dict(parity=p, seed_ids=ids, minimum=41, ties=0, closest=[])
                for ids in side.values()] for p, side in enumerate(classes)]
    histogram = [0] * 41
    partitions_seen = cosets = 0
    for blocks in partitions():
        partitions_seen += 1
        for t, minus, plus in placements(blocks, witness):
            cosets += 1
            parity = 1 ^ (t.bit_count() % 2)
            for seed, record in zip(classes[parity], records[parity]):
                missing = 20 - (seed & minus).bit_count()
                occupied = (seed & plus).bit_count()
                score = missing + occupied
                histogram[score] += 1
                histogram[40 - score] += 1
                best = min(score, 40 - score)
                if best > record["minimum"]:
                    continue
                if best < record["minimum"]:
                    record.update(minimum=best, ties=0, closest=[])
                for flip in (False, True):
                    if (40 - score if flip else score) == best:
                        record["ties"] += 1
                        record["closest"].append(dict(blocks=blocks, translation=t, reverse=flip,
                                                      missing=20-occupied if flip else missing,
                                                      occupied=20-missing if flip else occupied))
    total = sum(histogram)
    if partitions_seen != 1890 or cosets != 120960 or total != 120960 * sum(map(len, classes)):
        raise ValueError(("coverage", partitions_seen, cosets, total))
    result = dict(bank_sha256=sha256(BANK.read_bytes()).hexdigest(),
                  witness_sha256=sha256(WITNESS.read_bytes()).hexdigest(),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  unique_classes=list(map(len, classes)), partitions=partitions_seen,
                  signed_placements_per_parity=120960, comparisons=total, histogram=histogram,
                  classes=[r for side in records for r in side])
    (HERE / "seed-orbit.json").write_text(json.dumps(result, separators=(",", ":")) + "\n",
                                          encoding="utf-8", newline="\n")
    from collections import Counter
    print("comparisons", total, "histogram", histogram)
    print("class minima", sorted(Counter(r["minimum"] for r in result["classes"]).items()))
    print("closest placements retained", sum(r["ties"] for r in result["classes"]))


if __name__ == "__main__":
    main()
