"""Independent direct-vertex coverage audit for five missing Q9 counts.

Fix the distance-eight pair at 0 and 255. Enumerate every three-element
subset of the other 254 even vertices. This uses actual vertex combinations,
not the primary audit's coordinate-column compositions. Canonicalize only
the distinct resulting distance tuples under all 120 point permutations.

This checks the finite geometric metric catalogue. It does not check matrix
arithmetic, rebuild Lean, or itself assemble the whole-cube recovery theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import ctypes
import os
from datetime import datetime, timezone
from pathlib import Path
from time import perf_counter
from native_resources import snapshot, kernel, psapi, PROCESS_MEMORY_COUNTERS_EX


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    milestone = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=milestone / "data" / "five-count-audit.json")
    parser.add_argument("--output", type=Path, default=milestone / "data" / "independent-geometry.json")
    args = parser.parse_args()
    started = datetime.now(timezone.utc).isoformat()
    start = perf_counter()
    startup = snapshot()
    assert not startup['errors'] and not startup['processes'] and startup['free_bytes'] >= 1024**3
    peak = 0

    def guard():
        nonlocal peak
        state = snapshot()
        assert not state['errors'] and not state['processes'] and state['free_bytes'] >= 768 * 1024**2
        handle = kernel.OpenProcess(0x1000, False, os.getpid())
        assert handle
        counters = PROCESS_MEMORY_COUNTERS_EX()
        counters.cb = ctypes.sizeof(counters)
        try:
            assert psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb)
        finally:
            kernel.CloseHandle(handle)
        peak = max(peak, int(counters.PrivateUsage))
        assert peak <= 256 * 1024**2 and perf_counter() - start < 300
    source = json.loads(args.source.read_text(encoding="utf-8-sig"))
    expected = {tuple(row["distances"]) for row in source["metric_classes"]}

    # Translation puts one missing position at zero. Permuting coordinates
    # sends its distance-eight partner to 255 and preserves even parity.
    vertices = tuple(v for v in range(512) if v.bit_count() % 2 == 0 and v not in (0, 255))
    weights = {v: v.bit_count() for v in vertices}
    from_pair = {v: (v ^ 255).bit_count() for v in vertices}
    patterns: set[tuple[int, ...]] = set()
    descriptions = 0
    for a, b, c in itertools.combinations(vertices, 3):
        # Pair order is 01,02,03,04,12,13,14,23,24,34 for (0,255,a,b,c).
        patterns.add((8, weights[a], weights[b], weights[c],
                      from_pair[a], from_pair[b], from_pair[c],
                      (a ^ b).bit_count(), (a ^ c).bit_count(), (b ^ c).bit_count()))
        descriptions += 1
        if descriptions % 100000 == 0:
            guard()

    pairs = tuple(itertools.combinations(range(5), 2))
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    permutation_maps = tuple(
        tuple(pair_index[tuple(sorted((p[i], p[j])))] for i, j in pairs)
        for p in itertools.permutations(range(5))
    )
    canonical = {
        min(tuple(metric[i] for i in relabel) for relabel in permutation_maps)
        for metric in patterns
    }
    missing = sorted(expected - canonical)
    extra = sorted(canonical - expected)
    enumeration_complete = len(vertices) == 254 and descriptions == math.comb(254, 3)
    match = enumeration_complete and not missing and not extra
    metric_json = json.dumps(sorted(canonical), separators=(",", ":")).encode("ascii")
    guard()
    result = {
        "status": "PASS_GEOMETRIC_CLASS_COVERAGE" if match else "FAIL_GEOMETRIC_CLASS_COVERAGE",
        "started_utc": started,
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "seconds": perf_counter() - start,
        "startup_snapshot": startup,
        "peak_private_bytes": peak,
        "guard_sha256": sha256(Path(__file__).with_name('native_resources.py')),
        "method": "Direct combinations of actual even Q9 vertices after fixing the pair 0,255; canonicalization of unique distance tuples under all 120 point permutations.",
        "normalization_argument": "Translation sends one position to0; a coordinate permutation sends its distance8 partner to255. The other three positions are distinct even vertices outside that pair, and all such triples are enumerated.",
        "fixed_pair": [0, 255],
        "other_even_vertices": len(vertices),
        "vertex_triples": descriptions,
        "expected_vertex_triples": math.comb(254, 3),
        "enumeration_complete": enumeration_complete,
        "distinct_ordered_distance_tuples": len(patterns),
        "point_permutations": len(permutation_maps),
        "metric_class_count": len(canonical),
        "primary_metric_class_count": len(expected),
        "matches_primary_classes": not missing and not extra,
        "missing_primary_classes": missing,
        "extra_direct_classes": extra,
        "canonical_distance_tuples": sorted(canonical),
        "canonical_distances_sha256": hashlib.sha256(metric_json).hexdigest(),
        "source_path": str(args.source.resolve()),
        "source_sha256": sha256(args.source),
        "script_sha256": sha256(Path(__file__)),
        "scope": "Finite native geometric catalogue coverage only. No integer matrix implication or complete actual-cube Lean assembly is checked here.",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({k: result[k] for k in (
        "status", "vertex_triples", "distinct_ordered_distance_tuples",
        "metric_class_count", "matches_primary_classes", "seconds")}, indent=2))
    if not match:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
