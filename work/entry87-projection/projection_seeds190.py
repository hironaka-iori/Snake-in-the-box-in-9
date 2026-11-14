"""Relift the 1,042 published 190-edge sources and compare every improvement by symmetry."""
import csv, io, json
from collections import Counter
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile

from bank_pivots import canonical_word
from punctured_lift import project, solve
from solve import BANK, BANK_HASH, defects, save


def seeds():
    file = Path("public-records.zip")
    assert sha256(file.read_bytes()).hexdigest() == "7bd8ca971a52e6534670b6802d885f53bad0c31a6ba7117f2ba84ee458acb58e"
    with ZipFile(file) as archive:
        with archive.open("snakes_dim9_190.csv") as raw:
            for row in csv.DictReader(io.TextIOWrapper(raw)):
                vertices = list(map(int, row["vertices"].split()))
                assert len(vertices) == 191 and not defects(vertices)
                yield vertices


def run():
    assert sha256(BANK.read_bytes()).hexdigest() == BANK_HASH
    known = {canonical_word(r["vertex_sequence"]) for r in json.loads(BANK.read_bytes())}
    new = {}
    counts = Counter()
    records = []
    for index, q in enumerate(seeds()):
        for axis in range(9):
            P, old = project(q, axis)
            r = solve(P, 193-len(P))
            assert r["profile"][len(old)] > 0
            best = len(P) + max(r["profile"]) - 1
            counts[best] += 1
            if best < 191:
                continue
            for length in range(191, best+1):
                if length+1-len(P) not in r["profile"]:
                    continue
                hit = solve(P, length+1-len(P), False)["witness"]
                assert len(hit) == length+1 and not defects(hit)
                key = canonical_word(hit)
                if key not in known and key not in new:
                    new[key] = dict(source=index, axis=axis, edges=length, vertices=hit)
                    print("New class", index, axis, length, flush=True)
                records.append((index, axis, length, key in known))
            if best >= 192:
                save(Path("projected-190-improvement.json"), list(new.values()))
    assert (index+1)*9 == sum(counts.values()) == 1042*9
    save(Path("projected-190-census.json"), dict(maximum_lengths=counts,improvements=records,new_classes=list(new.values())))
    print("Maximum lengths", counts, "unknown classes", len(new), flush=True)


if __name__ == "__main__":
    run()
