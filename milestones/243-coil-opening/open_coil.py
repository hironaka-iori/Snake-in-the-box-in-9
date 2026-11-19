"""Complete or explicitly budgeted extension searches from arcs of a verified Q9 coil."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from seed_orbit import bits

ALL = (1 << 512) - 1
ADJ = [bits(v ^ (1 << i) for i in range(9)) for v in range(512)]


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def rotations(coil):
    """Find offsets certified by a cube isometry, allowing reversed cycle order."""
    maps = []
    for start in range(len(coil)):
        for sign in (1, -1):
            image = [coil[(start + sign * j) % 192] for j in range(192)]
            perm = {}
            for a, b, c, d in zip(coil, coil[1:], image, image[1:]):
                axis = a ^ b
                dest = c ^ d
                if axis in perm and perm[axis] != dest:
                    break
                perm[axis] = dest
            else:
                if len(perm) == len(set(perm.values())) == 9:
                    maps.append((start, sign))
    return maps


def verify(vertices_, cycle):
    length = len(vertices_)
    if any(not 0 <= v < 512 for v in vertices_) or len(set(vertices_)) != length:
        raise ValueError("Vertex labels or distinctness")
    if any(((a ^ b).bit_count() == 1) != (j-i == 1 or (cycle and j-i == length-1))
           for i, a in enumerate(vertices_) for j, b in enumerate(vertices_[i+1:], i+1)):
        raise ValueError("Adjacency or chord")


class BudgetReached(Exception):
    pass


def extensions(spine, target, budget):
    # Only the first vertex of each tail may touch the retained arc.
    closed = bits(spine)
    for v in spine:
        closed |= ADJ[v]
    free = ALL ^ closed
    def first_ports(endpoint):
        forbidden = bits(spine)
        for v in spine:
            if v != endpoint:
                forbidden |= ADJ[v]
        return ADJ[endpoint] & ~forbidden
    left_ports, right_ports = first_ports(spine[0]), first_ports(spine[-1])
    need = target - len(spine)
    nodes = 0
    best = len(spine)
    answer = None
    left, right = [], []
    def enter():
        nonlocal nodes, best, answer
        if nodes >= budget:
            raise BudgetReached
        nodes += 1
        size = len(spine) + len(left) + len(right)
        best = max(best, size)
        if size == target:
            answer = left[::-1] + spine + right
            verify(answer, False)
            return True
        return False

    def grow_right(options, available):
        if enter():
            return True
        for v in vertices(options):
            right.append(v)
            if grow_right(ADJ[v] & available, available & ~(ADJ[v] | (1 << v))):
                return True
            right.pop()
        return False

    def grow_left(options, available, remaining_ports):
        if grow_right(remaining_ports, available):
            return True
        for v in vertices(options):
            left.append(v)
            remove = ADJ[v] | (1 << v)
            if grow_left(ADJ[v] & available, available & ~remove, remaining_ports & ~remove):
                return True
            left.pop()
        return False

    try:
        found = grow_left(left_ports, free, right_ports)
        status = "witness" if found else "excluded"
    except BudgetReached:
        status = "unfinished"
    return dict(status=status, nodes=nodes, largest_verified_by_construction=best,
                extension_vertices_required=need, path=answer)


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("--spine", type=int, required=True)
    cli.add_argument("--budget", type=int, default=150000)
    args = cli.parse_args()
    if not 2 <= args.spine <= 191 or args.budget < 1:
        raise ValueError("Invalid retained arc or node budget")
    src = HERE / "coil9.json"
    coil, = json.loads(src.read_bytes())["q9_rows"]
    seq = coil["vertices"]
    if len(seq) != 192 or any((seq[j] ^ seq[(j+1) % 192]) != 1 << a
                              for j, a in enumerate(coil["actions"])) or len(coil["actions"]) != 192:
        raise ValueError("Cycle actions")
    verify(seq, True)
    syms = rotations(seq)
    pending = set(range(192))
    rows = []
    while pending:
        start = min(pending)
        orbit = sorted({(offset + sign * start - (args.spine-1 if sign < 0 else 0)) % 192
                        for offset, sign in syms})
        if not set(orbit) <= pending:
            raise ValueError("Overlapping start orbits")
        pending.difference_update(orbit)
        spine = [seq[(start+j) % 192] for j in range(args.spine)]
        outcome = extensions(spine, 193, args.budget)
        rows.append(dict(start=start, orbit=orbit, **outcome))
        if outcome["path"]:
            break
    result = dict(spine=args.spine, node_budget_per_representative=args.budget,
                  coil_sha256=sha256(src.read_bytes()).hexdigest(),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  symmetries=syms, rows=rows, starts_unqueried=sorted(pending))
    (HERE / f"arc-{args.spine}-{args.budget}.json").write_text(json.dumps(result, indent=2)+"\n",
                                                               encoding="utf-8", newline="\n")
    print(args.spine, "vertices retained;", len(rows), "orbits",
          dict(Counter(r["status"] for r in rows)), "nodes", sum(r["nodes"] for r in rows),
          "max vertices", max(r["largest_verified_by_construction"] for r in rows))


if __name__ == "__main__":
    main()
