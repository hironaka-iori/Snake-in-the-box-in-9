"""Transport fixed rooted 95-edge exclusions by exact inclusion under all axis permutations."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import permutations
import json
from math import factorial
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "252-shorter-reference-segments"
sys.path.insert(0, str(PRIOR))
from partners import canonical_root, file_hash, path_ok, read, shape


def maps():
    toggles = [bytes(v ^ (1<<j) for v in range(256)) for j in range(8)]
    for axes in permutations(range(8)):
        table = b"\0"
        for axis in axes:
            table += table.translate(toggles[axis])
        yield axes, table


def image(vertex, axes):
    return sum(1 << axes[i] for i in range(8) if vertex & (1<<i))


def targets(closure, previous):
    roots = []
    paths = read(closure)["paths"]
    old = set(read(previous)["all_ids"])
    if not old <= paths.keys():
        raise ValueError("Missing earlier parents from closure")
    for key in sorted(paths.keys()-old):
        path = paths[key]
        if len(path) != 97:
            continue
        path_ok(path, 8)
        if sha256(shape(path)).hexdigest() != key:
            raise ValueError("Parent identifier mismatch")
        for end, oriented in enumerate((path, path[::-1])):
            root_key, rooted, axes = canonical_root(oriented)
            if rooted != [image(v ^ oriented[0], axes) for v in oriented]:
                raise ValueError("Incorrect rooted coordinate map")
            roots.append((dict(shape=key, end=end, original_root=oriented[0],
                               root_id=root_key, raw_to_canonical_axes=axes), set(rooted[1:])))
    return roots


def search(blocked, roots, presence, tables):
    need = Counter(v.bit_count() for v in blocked)
    possible = 0
    for j,(_, sites) in enumerate(roots):
        counts = Counter(v.bit_count() for v in sites)
        if all(counts[w] >= n for w,n in need.items()):
            possible |= 1<<j
    # Select sparse Hamming shells first. They eliminate the largest fraction
    # of roots per checked vertex on average over the full permutation group.
    density = {w: sum((presence[v] & possible).bit_count() for v in range(256) if v.bit_count()==w)
               / sum(v.bit_count()==w for v in range(256)) for w in need}
    order = sorted(blocked, key=lambda v:(density[v.bit_count()], v))
    answers = {}
    for axes, table in tables:
        if not possible:
            break
        eligible = possible
        for v in order:
            eligible &= presence[table[v]]
            if not eligible:
                break
        possible ^= eligible
        while eligible:
            low = eligible & -eligible
            idx = low.bit_length()-1
            if not {image(v,axes) for v in blocked} <= roots[idx][1]:
                raise ValueError("Reported transported set is not contained in the full parent")
            answers[idx] = list(axes)
            eligible ^= low
    return answers


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--input", default="group-caps.json")
    cli.add_argument("--output", default="transports.json")
    args = cli.parse_args()
    pool = HERE/args.input
    closure = HERE/"closure.json"
    previous = PRIOR/"census-68.json"
    roots = targets(closure, previous)
    records = read(pool)["records"]
    presence = [0]*256
    for j,(_, sites) in enumerate(roots):
        for v in sites:
            presence[v] |= 1<<j
    tables = list(maps())
    if len(tables) != factorial(8):
        raise ValueError("Missing coordinate permutations")
    coverage = {}
    by_root = [{} for _ in roots]
    for digest,row in sorted(records.items()):
        if row["status"] != "excluded":
            continue
        blocked = row["blocked"]
        if blocked != sorted(set(blocked)) or not all(0 < v < 256 for v in blocked):
            raise ValueError("Invalid blocked set")
        matches = search(blocked, roots, presence, tables)
        coverage[digest] = len(matches)
        for idx, axes in matches.items():
            by_root[idx][digest] = axes
    count = [len(x) for x in by_root]
    results = [dict(**meta,witnesses=proofs) for (meta,_),proofs in zip(roots,by_root)]
    files = [pool,closure,previous,Path(__file__),PRIOR/"partners.py",
             HERE.parent/"251-eighty-edge-segments"/"partners251.py",
             HERE.parent/"249-long-parent-joins"/"geometry.py"]
    out = dict(partner_edges=95,pins={p.relative_to(HERE.parents[1]).as_posix():file_hash(p) for p in files},
               shape_count=len(roots)//2,roots=len(roots),covered=sum(bool(n) for n in count),
               uncovered=count.count(0),certificate_count=len(coverage),axis_permutations=len(tables),
               roots_per_certificate=coverage,results=results)
    (HERE/args.output).write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("Certificates", len(coverage), "covered roots", out["covered"], "uncovered", out["uncovered"])


if __name__ == "__main__":
    main()
