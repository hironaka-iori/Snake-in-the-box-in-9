"""Replay the finite face exclusions and the reduction to the nine-cube path bound."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

from dense_facet_audit import audit as audit_dense
from edge_window import check as audit_window
from edge_rich_faces import read_shapes
from solve import BANK, BANK_HASH, save


def four_cube():
    adj = [sum(1 << (v ^ (1<<i)) for i in range(4)) for v in range(16)]
    counts = Counter()
    for mask in range(1<<16):
        vertices = [v for v in range(16) if mask & (1<<v)]
        degree = [(mask & adj[v]).bit_count() for v in vertices]
        if max(degree, default=0) > 2:
            continue
        rest = mask
        for root, deg in zip(vertices,degree):
            if deg > 1 or not (rest & (1<<root)):
                continue
            v = root
            while rest & (1<<v):
                rest ^= 1<<v
                following = rest & adj[v]
                if not following:
                    break
                v = (following & -following).bit_length()-1
        if not rest:
            counts[len(vertices)] += 1
    assert max(counts) == 8 and counts[8] == 922
    return counts


def main(checker):
    assert checker.is_file()
    small = four_cube()
    dense = audit_dense(True, checker)
    assert {n:(r["classes"],r["excluded"]) for n,r in dense.items()} == {
        62:(192,192), 63:(18,18), 64:(6,6)}
    expected = {57:339,58:256,59:212,60:147}
    observed = {n:sum(1 for _ in read_shapes(n,46)) for n in expected}
    assert observed == expected
    assert sum(1 for _ in read_shapes(61,0)) == 1630
    packed = Path("edge-window-117-104-all.weights.gz")
    assert packed.is_file()
    window = audit_window(117,104,True,packed,"all",checker)
    assert not window["open_cases"] and window["minimum_face_edges"] == 46
    assert sum(window["methods"].values()) == 216+1630+sum(expected.values())
    # For a 232-edge path, delete the least-used direction. Runs alternate
    # and each side therefore has at most 13 components. Restricting to
    # exactly 117 vertices by deleting tips never increases that count.
    target = 232
    max_crossings = target//9
    max_runs_one_side = (max_crossings+2)//2
    heavier_half = (target+2)//2
    assert (max_crossings,max_runs_one_side,heavier_half) == (25,13,117)
    assert 117-max_runs_one_side == 104 and 16*45 < 7*104
    raw = BANK.read_bytes()
    assert sha256(raw).hexdigest() == BANK_HASH
    snake = json.loads(raw)[0]["vertex_sequence"]
    assert len(set(snake)) == len(snake) == 192 and all(0 <= v < 512 for v in snake)
    pairs = 0
    for i,v in enumerate(snake):
        for j,u in enumerate(snake[:i]):
            assert (((v^u).bit_count() == 1) == (i-j == 1))
            pairs += 1
    assert pairs == 18336
    return dict(q9_lower=len(snake)-1, lower_bound_bank_entry=0, vertex_pairs_checked=pairs,
                q9_upper=target-1, excluded_edges=target, heavier_half=heavier_half,
                component_limit=max_runs_one_side, q4_max_vertices=max(small),
                dense_classes={n:r["classes"] for n,r in dense.items()},
                edge_rich_classes=observed, final_methods=window["methods"],
                resolution_proofs_in_final_window=len(window["resolution_receipts"]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--checker", type=Path, required=True)
    args = parser.parse_args()
    result = main(args.checker.resolve())
    save(Path("q9-density-verification.json"), result)
    print(json.dumps(result,sort_keys=True))
