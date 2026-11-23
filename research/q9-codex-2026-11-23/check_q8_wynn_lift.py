"""Compute the edge-count obstruction for lifting a Q8 snake with either Wynn arm."""
import argparse
import itertools
import json
from pathlib import Path
from search_q9_wynn_plateau import WYNN, verify


def minimum_overlap(lower, arms):
    translations = [sum(1 << (v ^ t) for v in lower) for t in range(256)]
    minima = [256] * len(arms)
    for permutation in itertools.permutations(range(8)):
        image = [0] * 256
        for v in range(1, 256):
            bit = v & -v
            image[v] = image[v ^ bit] | (1 << permutation[bit.bit_length() - 1])
        for i, arm in enumerate(arms):
            mask = sum(1 << image[v] for v in arm)
            minima[i] = min(minima[i], min((mask & other).bit_count() for other in translations))
    return minima


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("q8_witness", type=Path)
    args = parser.parse_args()
    lower = json.loads(args.q8_witness.read_text())["vertex_sequence"]
    assert len(lower) == 99 and max(lower) < 256 and verify(lower)
    arms = []
    for steps in WYNN.split("8"):
        path = [0]
        for step in steps:
            path.append(path[-1] ^ (1 << int(step)))
        assert verify(path)
        arms.append(path)
    for arm, overlap in zip(arms, minimum_overlap(lower, arms)):
        # A union of two paths on V vertices has V-2+m edges, maximum degree 3.
        # Keeping an induced path after k deletions requires m <= 2k+1.
        min_removed = overlap // 2
        print({"arm_edges": len(arm)-1, "min_overlap": overlap,
               "upper_bound_edges": len(lower)+len(arm)-1-min_removed})


if __name__ == "__main__":
    main()
