"""Explore neutral moves and extensions starting at Wynn's published Q9 190-snake."""
import argparse
import json
from collections import Counter, deque
from pathlib import Path

# Wynn, arXiv:1201.1647, Appendix, snake d=9.
WYNN = "0120314021054102143210264314504134210431450143273120143012632143053102305314503604314021431046806104314501431063021432035043203145365403140543753140214310451341021431650453145041204501430540"
NB = [tuple(v ^ (1 << i) for i in range(9)) for v in range(512)]


def verify(path):
    return (len(path) == len(set(path)) and all(0 <= v < 512 for v in path)
            and all(((u ^ path[j]).bit_count() == 1) == (i + 1 == j)
                    for i, u in enumerate(path) for j in range(i + 1, len(path))))


def canonical(path):
    steps = bytes((u ^ v).bit_length() - 1 for u, v in zip(path, path[1:]))
    keys = []
    for word in (steps, steps[::-1]):
        labels = {}
        keys.append(bytes(labels.setdefault(c, len(labels)) for c in word))
    return min(keys)


def moves(path, floor=190):
    used = set(path)
    degree = Counter(v for x in path for v in NB[x])
    for p in (path, path[::-1]):
        if len(p) - 1 > floor:
            yield p[:-1]
        for v in NB[p[-1]]:
            if v in used:
                continue
            if degree[v] == 1:
                yield p + (v,)
            if degree[v] - (p[0] in NB[v]) == 1:
                yield p[1:] + (v,)
        for v in NB[p[-2]]:
            if v not in used and degree[v] - (p[-1] in NB[v]) == 1:
                yield p[:-1] + (v,)
    for i in range(1, len(path) - 1):
        v = path[i - 1] ^ path[i] ^ path[i + 1]
        if v not in used and degree[v] == 2:
            yield path[:i] + (v,) + path[i + 1:]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("bank", type=Path)
    parser.add_argument("--limit", type=int, default=30000)
    parser.add_argument("--floor", type=int, default=190, choices=range(180, 191))
    args = parser.parse_args()
    bank = [tuple(row["vertex_sequence"]) for row in json.loads(args.bank.read_text())]
    assert verify(bank[0]) and bank[0] in set(moves(bank[0][:-1]))
    known = {canonical(p) for p in bank}
    seed = [0]
    for digit in WYNN:
        seed.append(seed[-1] ^ (1 << int(digit)))
    seed = tuple(seed)
    assert verify(seed) and len(seed) == 191
    queue = deque([seed])
    seen = {canonical(seed)}
    classes = Counter({190: 1})
    expanded = new191 = 0
    while queue and expanded < args.limit:
        p = queue.popleft()
        expanded += 1
        for q in moves(p, args.floor):
            key = canonical(q)
            if key in seen:
                continue
            seen.add(key)
            if len(q) >= 192:
                assert verify(q)
                if len(q) >= 193:
                    print(json.dumps({"vertices": q, "edges": len(q)-1}), flush=True)
                    return
                new191 += key not in known
                queue.appendleft(q)
            else:
                queue.append(q)
            classes[len(q)-1] += 1
    print(dict(expanded=expanded, frontier=len(queue), classes=dict(classes), new191=new191))


if __name__ == "__main__":
    main()
