"""Repartition each rooted projected union after adding one odd vertex.

For the nonroot graph G, let a(v) indicate adjacency to the root and put
M = adjacency(G) + diag(deg_G + 2a - 4). If the even outer endpoint p is
coloured +1 and the odd endpoint q is -1, the required degrees give
M c = -2(e_p-e_q). Interchanging arm colours always permits this convention.
Reduce modulo 3: the two nonzero residues have unique sign representatives.
Enumerate the nonzero values of the free variables after exact elimination.
Rebuild the induced graph of each arm for every surviving modular candidate.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
from time import monotonic
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "243-coil-opening"))
from open_coil import verify

NEIGHBOURS = [tuple(v ^ (1 << i) for i in range(8)) for v in range(256)]


def add(first, second):
    """Add vectors over F3; the two integer masks mark residues 1 and 2."""
    a, b = first
    c, d = second
    azero, czero = ~(a | b), ~(c | d)
    return (azero & c) | (a & czero) | (b & d), (azero & d) | (b & czero) | (a & c)


def negative(vector):
    return vector[1], vector[0]


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def eliminate(points, union):
    """Return one RHS column per vertex and a basis indexed by free variables.

    Slots 0,...,n-1 describe variable values. Slots n and above are residual
    equations that a proposed right-hand side must satisfy.
    """
    n = len(points)
    index = {v: i for i, v in enumerate(points)}
    rows = []
    for i, v in enumerate(points):
        adjacent = [index[t] for t in NEIGHBOURS[v] if t in union and t != 0]
        ones = sum(1 << t for t in adjacent) | (1 << (n + i))
        twos = 0
        diagonal = (len(adjacent) + 2 * (0 in NEIGHBOURS[v]) - 4) % 3
        if diagonal == 1:
            ones |= 1 << i
        elif diagonal == 2:
            twos |= 1 << i
        rows.append((ones, twos))
    pivots, free = [], []
    for column in range(n):
        bit = 1 << column
        rank = len(pivots)
        pivot = next((i for i in range(rank, n) if (rows[i][0] | rows[i][1]) & bit), None)
        if pivot is None:
            free.append(column)
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        if rows[rank][1] & bit:
            rows[rank] = negative(rows[rank])
        pivot_row = rows[rank]
        minus_pivot = negative(pivot_row)
        for i, row in enumerate(rows):
            if i == rank:
                continue
            if row[0] & bit:
                rows[i] = add(row, minus_pivot)
            elif row[1] & bit:
                rows[i] = add(row, pivot_row)
        pivots.append(column)
    slots = pivots + list(range(n, n + len(free)))
    rhs = [[0, 0] for _ in range(n)]
    for row, slot in zip(rows, slots):
        for residue in (0, 1):
            for column in positions(row[residue] >> n):
                rhs[column][residue] |= 1 << slot
    kernel = []
    for j in free:
        bit = 1 << j
        ones, twos = bit, 0
        for i, slot in enumerate(pivots):
            if rows[i][0] & bit:
                twos |= 1 << slot
            elif rows[i][1] & bit:
                ones |= 1 << slot
        kernel.append((ones, twos))
    return rhs, kernel


def arm_path(selected, end):
    """Return the unique root-to-end induced traversal, or reject the colours."""
    path = [0]
    seen = {0}
    while True:
        v = path[-1]
        adjacent = [t for t in NEIGHBOURS[v] if t in selected]
        if len(adjacent) != (1 if v in (0, end) else 2):
            return None
        if v == end:
            return path if seen == selected else None
        remaining = [t for t in adjacent if t not in seen]
        if len(remaining) != 1:
            return None
        seen.add(remaining[0])
        path.append(remaining[0])


def witness(points, ones, p, q):
    positive = {points[i] for i in positions(ones)} | {0}
    negative_set = (set(points) - positive) | {0}
    first = arm_path(positive, points[p])
    if first is None:
        return None
    second = arm_path(negative_set, points[q])
    if second is None:
        return None
    path = first[::-1] + [256 + v for v in second]
    if len(path) != 193 or set(first) & set(second) != {0}:
        raise ValueError("Invalid projected arm size or intersection")
    verify(first, False)
    verify(second, False)
    verify(path, False)
    return dict(arms=[first, second], q9=path, arm_lengths=[len(first)-1, len(second)-1])


def search(union, limit):
    points = sorted(union - {0})
    n = len(points)
    rhs, kernel = eliminate(points, union)
    full = (1 << n) - 1
    influence = 0
    for ones, twos in kernel:
        influence |= ones | twos
    fixed = full ^ influence
    odd = defaultdict(list)
    for q, v in enumerate(points):
        if v.bit_count() % 2:
            odd[rhs[q][0] >> n, rhs[q][1] >> n].append(q)
    candidates = []
    consistent = 0
    for p, v in enumerate(points):
        if v.bit_count() % 2:
            continue
        for q in odd[rhs[p][0] >> n, rhs[p][1] >> n]:
            consistent += 1
            base = add(rhs[p], negative(rhs[q]))
            if fixed & ~(base[0] | base[1]):
                continue
            if fixed & (1 << p) and not (base[0] & (1 << p)):
                continue
            if fixed & (1 << q) and not (base[1] & (1 << q)):
                continue
            candidates.append((p, q, base))

    dimension = len(kernel)
    total = len(candidates) * (1 << dimension)
    record = dict(nullity=dimension, compatible_endpoint_pairs=consistent,
                  surviving_endpoint_pairs=len(candidates), potential_trials=total,
                  trials=0, exact_graph_checks=0)
    if candidates:
        shift = (0, 0)
        for direction in kernel:
            shift = add(shift, negative(direction))
        # Gray order changes one free sign at a time, starting with all minus.
        for i in range(1 << dimension):
            if i:
                j = (i & -i).bit_length() - 1
                positive = ((i ^ (i >> 1)) >> j) & 1
                shift = add(shift, negative(kernel[j]) if positive else kernel[j])
            for p, q, base in candidates:
                if record["trials"] >= limit:
                    return dict(record, status="unknown_trial_limit")
                record["trials"] += 1
                ones, twos = add(base, shift)
                if (ones | twos) != full or not (ones & (1 << p)) or not (twos & (1 << q)):
                    continue
                record["exact_graph_checks"] += 1
                path = witness(points, ones, p, q)
                if path is not None:
                    return dict(record, status="verified_witness", witness=path)
    return dict(record, status="excluded")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=0, help="First input pair index, inclusive")
    parser.add_argument("--stop", type=int, default=None, help="Last input pair index, exclusive")
    parser.add_argument("--trials", type=int, default=100000, help="Maximum modular assignments per distinct case")
    args = parser.parse_args()
    data_path = HERE / "comparison.json"
    data = data_path.read_bytes()
    pairs = json.loads(data)["one_crossing_pairs"]
    stop = len(pairs) if args.stop is None else args.stop
    if not (0 <= args.start < stop <= len(pairs) and args.trials > 0):
        parser.error("Invalid range or trial budget")
    suffix = "" if args.start == 0 and stop == len(pairs) else f"-{args.start}-{stop}"
    destination = HERE / ("repartition" + suffix + ".json")
    temporary = destination.with_suffix(".tmp")
    results, cache = [], {}
    record = dict(comparison_sha256=sha256(data).hexdigest(),
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  start=args.start, stop=stop, trial_limit=args.trials,
                  input_pair_count=len(pairs), results=results)

    def save():
        record["distinct_cases"] = len(cache)
        record["status_counts"] = dict(Counter(r["status"] for r in results))
        temporary.write_text(json.dumps(record, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
        temporary.replace(destination)

    start_time = monotonic()
    for i in range(args.start, stop):
        entry = pairs[i]
        first, second = entry["long"], entry["short"]
        union = set(first) | set(second)
        if (first[0], second[0], len(union)) != (0, 0, 191) or set(first) & set(second) != {0}:
            raise ValueError("Input is not a normalized 191-vertex projection")
        additions = [v for v in range(256) if v not in union and v.bit_count() % 2 and v not in NEIGHBOURS[0]]
        if len(additions) != 27:
            raise ValueError("Expected 27 admissible additions")
        for x in additions:
            enlarged = frozenset(union | {x})
            if enlarged in cache:
                origin, outcome = cache[enlarged]
                row = dict(status=outcome["status"], duplicate_of=origin)
            else:
                row = search(enlarged, args.trials)
                cache[enlarged] = (len(results), row)
            results.append(dict(pair=i, seed=entry["seed"], axis=entry["axis"], addition=x, **row))
            if row["status"] == "verified_witness":
                save()
                print("Verified 192-edge path", i, x, destination, flush=True)
                return
        save()
        print("Through input pair", i, "distinct unions", len(cache), "results", record["status_counts"],
              "seconds", round(monotonic()-start_time, 2), flush=True)


if __name__ == "__main__":
    main()
