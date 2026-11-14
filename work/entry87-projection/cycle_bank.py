"""Classify cycles cut out by the 180 single-chord insertions."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from solve import BANK, BANK_HASH, defects, save, sha256


def canonical(cycle):
    moves = [(x^y).bit_length()-1 for x,y in zip(cycle,cycle[1:]+cycle[:1])]
    images = []
    for order in (moves,moves[::-1]):
        for pos in range(len(order)):
            names = {}
            image = tuple(names.setdefault(x,len(names)) for x in order[pos:]+order[:pos])
            images.append(image)
    return min(images)


def census():
    raw = BANK.read_bytes()
    assert sha256(raw).hexdigest() == BANK_HASH
    bank = json.loads(raw)
    rows = json.loads(Path("bank-pivots.json").read_text())
    classes = {}
    for k,row in enumerate(rows):
        path = bank[row["entry"]]["vertex_sequence"]
        t = row["insertion"]
        q = path[:t+1] + [v^(1<<row["flip"]) for v in path[t:]]
        assert defects(q) == [tuple(row["chord"])]
        a,b = row["chord"][:2]
        cycle = q[a:b+1]
        for i,j in combinations(range(len(cycle)),2):
            distance=(cycle[i]^cycle[j]).bit_count()
            assert distance == 1 if j==i+1 or (i==0 and j+1==len(cycle)) else distance>=2
        key = canonical(cycle)
        if key not in classes:
            classes[key] = dict(cycle=cycle, references=[])
        classes[key]["references"].append(k)
    result = sorted(classes.values(),key=lambda r:(-len(r["cycle"]),r["references"][0]))
    return result


if __name__ == "__main__":
    classes = census()
    save(Path("cycle-bank.json"),classes)
    print(sorted(Counter(len(r["cycle"]) for r in classes).items(),reverse=True))
