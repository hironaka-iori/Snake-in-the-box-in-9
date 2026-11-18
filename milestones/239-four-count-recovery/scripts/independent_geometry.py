"""Enumerate actual Q9 vertices to audit four-point distance coverage.

This script is independent of the weak-composition enumeration.  It compares
distance patterns only; equality of patterns need not imply cube isometry.
The six distances are ordered as 01, 02, 03, 12, 13, 23 throughout.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
from itertools import permutations
import json
from math import comb
from pathlib import Path
from time import perf_counter_ns


EDGES = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
EDGE_INDEX = {edge: i for i, edge in enumerate(EDGES)}
PERMUTED_INDICES = tuple(
    tuple(EDGE_INDEX[tuple(sorted((p[i], p[j])))] for i, j in EDGES)
    for p in permutations(range(4))
)


def canonical(distances: tuple[int, ...]) -> tuple[int, ...]:
    """Lexicographically least distance tuple over all point permutations."""
    return min(tuple(distances[i] for i in order) for order in PERMUTED_INDICES)


def input_metrics(payload: dict) -> tuple[set[tuple[int, ...]], int, int]:
    rows = payload["metric_classes"]
    if not isinstance(rows, list):
        raise ValueError("metric_classes must be an array")
    normalized = set()
    noncanonical_rows = 0
    for index, row in enumerate(rows):
        distances = row["distances"]
        if not isinstance(distances, list) or len(distances) != len(EDGES):
            raise ValueError(f"metric_classes[{index}].distances must have six entries")
        if any(type(d) is not int or d not in (2, 4, 6, 8) for d in distances):
            raise ValueError(f"metric_classes[{index}] has an invalid same-parity distance")
        metric = tuple(distances)
        representative = canonical(metric)
        noncanonical_rows += representative != metric
        normalized.add(representative)
    return normalized, len(rows), noncanonical_rows


def enumerate_metrics() -> tuple[set[tuple[int, ...]], int]:
    """Visit each unordered triple of nonzero even vertices exactly once."""
    vertices = tuple(v for v in range(1, 512) if v.bit_count() % 2 == 0)
    weights = tuple(v.bit_count() for v in vertices)
    pair_distances = tuple(
        tuple((a ^ b).bit_count() for b in vertices) for a in vertices
    )
    raw_metrics = set()
    triples = 0
    size = len(vertices)
    for i in range(size - 2):
        ai = pair_distances[i]
        for j in range(i + 1, size - 1):
            bj = pair_distances[j]
            first, second, fourth = weights[i], weights[j], ai[j]
            for k in range(j + 1, size):
                raw_metrics.add(
                    (first, second, weights[k], fourth, ai[k], bj[k])
                )
                triples += 1
    return raw_metrics, triples


def main() -> int:
    here = Path(__file__).resolve()
    milestone = here.parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input", type=Path, default=milestone / "data/four-count-audit.json"
    )
    parser.add_argument(
        "--output", type=Path, default=milestone / "data/independent-geometry.json"
    )
    args = parser.parse_args()
    started = perf_counter_ns()
    input_path = args.input.resolve()
    input_bytes = input_path.read_bytes()
    payload = json.loads(input_bytes)
    expected, input_rows, noncanonical_rows = input_metrics(payload)

    raw_metrics, total_triples = enumerate_metrics()
    actual = {canonical(metric) for metric in raw_metrics}
    expected_triples = comb(255, 3)
    equality = actual == expected
    complete_triple_count = total_triples == expected_triples
    report = {
        "status": "PASS_GEOMETRY_COVERAGE"
        if equality and complete_triple_count
        else "FAIL_GEOMETRY_COVERAGE",
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "dimension": 9,
        "fixed_first_vertex": 0,
        "other_vertices": "All 255 nonzero even-weight nine-bit vertices",
        "pair_order": [list(edge) for edge in EDGES],
        "point_permutations": len(PERMUTED_INDICES),
        "total_triples": total_triples,
        "expected_total_triples": expected_triples,
        "complete_triple_count": complete_triple_count,
        "raw_distance_tuples": len(raw_metrics),
        "metric_classes": len(actual),
        "input_metric_rows": input_rows,
        "input_canonical_metric_classes": len(expected),
        "input_noncanonical_rows": noncanonical_rows,
        "input_duplicate_canonical_rows": input_rows - len(expected),
        "metric_sets_equal": equality,
        "canonical_distance_tuples": [list(metric) for metric in sorted(actual)],
        "missing_from_input": [list(metric) for metric in sorted(actual - expected)],
        "absent_from_vertex_enumeration": [
            list(metric) for metric in sorted(expected - actual)
        ],
        "source_and_input_hashes": {
            str(here): hashlib.sha256(here.read_bytes()).hexdigest(),
            str(input_path): hashlib.sha256(input_bytes).hexdigest(),
        },
        "runtime_ns": perf_counter_ns() - started,
        "solver_used": False,
        "floating_point_arithmetic_used": False,
        "scope": (
            "Independent coverage audit of all six-distance patterns for four "
            "distinct vertices in one parity class of Q9. Translation by any "
            "chosen first vertex fixes it at zero and makes all three other "
            "vertices even. Enumerating their unordered triples loses no "
            "distance pattern after point-permutation canonicalization."
        ),
        "limitations": [
            "Distance patterns may identify configurations that are not cube-isometric.",
            "This native enumeration is separate from Lean checking of the finite arithmetic.",
            "This audit alone proves neither recovery nor a snake bound; it verifies coverage.",
            "Mixed-parity four-point configurations are outside this enumeration.",
        ],
    }
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": report["status"],
                "total_triples": total_triples,
                "raw_distance_tuples": len(raw_metrics),
                "metric_classes": len(actual),
                "metric_sets_equal": equality,
                "runtime_ns": report["runtime_ns"],
                "output": str(output),
            },
            indent=2,
        )
    )
    return 0 if equality and complete_triple_count else 1


if __name__ == "__main__":
    raise SystemExit(main())
