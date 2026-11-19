"""Enumerate induced Q9 paths keeping exactly 190 vertices of a recorded 190-edge parent."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import csv
import json
import sys
import zipfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "243-coil-opening"))
from open_coil import ADJ, bits, verify, vertices


def complete(parent, parent_mask, index):
    forbidden = 1 << parent[index]
    retained = parent_mask ^ forbidden
    best = -1
    bridges = 0

    def tails(left, right, mask, remaining, allow_left, left_tail, right_tail, spine):
        nonlocal best
        best = max(best, mask.bit_count() - 1)
        if remaining == 0:
            path = list(reversed(left_tail)) + spine() + right_tail
            if len(path) != 193 or (bits(path) & parent_mask) != retained:
                raise ValueError("Incorrect exchange")
            verify(path, False)
            return path
        for side in ([0, 1] if allow_left else [1]):
            endpoint = (left, right)[side]
            for z in vertices(ADJ[endpoint] & ~(mask | forbidden)):
                if (ADJ[z] & mask) != (1 << endpoint):
                    continue
                if side == 0:
                    path = tails(z, right, mask | (1 << z), remaining - 1,
                                 True, left_tail + [z], right_tail, spine)
                else:
                    path = tails(left, z, mask | (1 << z), remaining - 1,
                                 False, left_tail, right_tail + [z], spine)
                if path:
                    return path

    if index in (0, len(parent) - 1):
        run = parent[1:] if index == 0 else parent[:-1]
        path = tails(run[0], run[-1], retained, 3, True, [], [], lambda: run)
        return best, bridges, path

    for reverse_left in range(1 + (index > 1)):
        a, outer_left = ((parent[index - 1], parent[0]) if not reverse_left
                         else (parent[0], parent[index - 1]))
        for reverse_right in range(1 + (index < len(parent) - 2)):
            b, outer_right = ((parent[index + 1], parent[-1]) if not reverse_right
                              else (parent[-1], parent[index + 1]))

            def join(previous, mask, middle, remaining):
                nonlocal bridges
                if (previous ^ b).bit_count() > remaining + 1:
                    return
                for z in vertices(ADJ[previous] & ~(mask | forbidden)):
                    if (z ^ b).bit_count() > remaining:
                        continue
                    touch = ADJ[z] & mask
                    if touch == ((1 << previous) | (1 << b)):
                        bridges += 1
                        def spine():
                            left, right = parent[:index], parent[index + 1:]
                            return (left[::-1] if reverse_left else left) + middle + [z] + (
                                right[::-1] if reverse_right else right)
                        path = tails(outer_left, outer_right, mask | (1 << z),
                                     remaining - 1, True, [], [], spine)
                    elif remaining > 1 and touch == (1 << previous):
                        path = join(z, mask | (1 << z), middle + [z], remaining - 1)
                    else:
                        continue
                    if path:
                        return path

            path = join(a, retained, [], 3)
            if path:
                return best, bridges, path
    return best, bridges, None


def main():
    previous = json.loads((HERE.parent / "244-190-path-construction/results.json").read_bytes())
    with zipfile.ZipFile(HERE.parents[1] / "work/record_snakes.csv.zip") as archive:
        raw = archive.read("snakes_dim9_190.csv")
    if sha256(raw).hexdigest() != previous["member_sha256"]:
        raise ValueError("Parent collection differs from Round 244")
    rows = []
    total = Counter()
    witness = None
    for i, row in enumerate(csv.DictReader(raw.decode().splitlines())):
        parent = list(map(int, row["vertices"].split()))
        parent_mask = bits(parent)
        lengths = Counter()
        bridges = 0
        for j in range(len(parent)):
            best, count, path = complete(parent, parent_mask, j)
            lengths[best] += 1
            bridges += count
            if path:
                witness = dict(parent=i, deleted_index=j, path=path)
                break
        rows.append(dict(parent=i, best_by_deletion=lengths, bridges=bridges))
        total.update(lengths)
        if witness:
            break
    record = dict(input_sha256=previous["member_sha256"], code_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  cases=sum(total.values()), best_by_deletion=total, witness=witness, parents=rows)
    (HERE / "one-loss.json").write_text(json.dumps(record, separators=(",", ":")) + "\n",
                                            encoding="utf-8", newline="\n")
    print("parents", len(rows), "deletions", record["cases"], "best-length distribution", dict(total))


if __name__ == "__main__":
    main()
