"""Examine seven-cube faces selected by their internal edge count."""
import argparse
import json
from pathlib import Path

from dense_eight import components, facet_completion
from forest_orbit_weights import bound
from solve import save


def read_shapes(n, minimum):
    full = Path(f"seven-face-classes-{n}.txt")
    file = full if full.exists() else Path(f"rich-46-classes-{n}.txt")
    if file != full and minimum < 46:
        raise ValueError("The restricted census starts at 46 edges")
    for i, line in enumerate(file.read_text().splitlines()):
        a, b, c, weight, stabilizer = map(int, line.split())
        if n - c < minimum:
            continue
        mask = a | (b << 64)
        vertices = [v for v in range(128) if (mask >> v) & 1]
        parts = components(set(vertices), 7)
        assert len(vertices) == n and len(parts) == c and weight*stabilizer == 645120
        assert all(e == len(part)-1 for e, part in parts)
        yield i, vertices, n-c


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("minimum", type=int)
    parser.add_argument("--target-edges", type=int, default=104)
    parser.add_argument("--budget", type=int, default=750000)
    parser.add_argument("--checker", type=Path)
    parser.add_argument("--weights-only", action="store_true")
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    for i, vertices, edges in read_shapes(args.n, args.minimum):
        weight = Path(f"individual-weight-{args.n}-{i}.json")
        if weight.exists():
            record = json.loads(weight.read_bytes())
            assert record["fixed"] == vertices and record["size"] == 117
            if args.replay:
                assert bound(set(vertices), 117, record["certificate"]) == record
        else:
            record = bound(set(vertices), 117)
            save(weight, record)
        if record["max_edges"] < args.target_edges or args.weights_only:
            print(args.n, i, edges, record["max_edges"], flush=True)
            continue
        tag = f"edge-rich-{args.n}-{i}-{args.target_edges}-{args.budget}"
        checker = args.checker.resolve() if args.checker else None
        if checker:
            tag += "-checked"
        if not Path(tag+".json").exists():
            facet_completion(vertices, 117, 117-args.target_edges, args.budget, tag, checker, True)
