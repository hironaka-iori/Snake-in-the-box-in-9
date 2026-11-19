"""Free both outer pieces on both faces for a fixed pair of Q7 middles.

The Q9 label is u + 128*y + 256*x. At y=1 exactly the two given middles
are selected. At y=0 the two x-faces intersect in precisely the chosen q.
"""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "243-coil-opening"
sys.path.insert(0, str(SOURCE))
from arc_sat import Formula, connected_parts
from open_coil import verify

SOLVER = Path("D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe")
NEIGHBOURS = [tuple(v ^ (1 << j) for j in range(9)) for v in range(512)]


def bounds(cnf, neighbours, low, high, prefix):
    if high < 0 or low > len(neighbours):
        cnf.clauses.append(prefix)
        return
    if high < len(neighbours):
        for group in combinations(neighbours, high + 1):
            cnf.clauses.append(prefix + [-lit for lit in group])
    if low > 0:
        for group in combinations(neighbours, len(neighbours) - low + 1):
            cnf.clauses.append(prefix + list(group))


def encode(middles, q):
    outer = {u+256*x for x in (0, 1) for u in range(128) if u not in middles[x][1:-1]}
    forced = {u+256*x for x, mid in enumerate(middles) for u in (mid[0], mid[-1], q)}
    fixed = forced | {128+256*x+u for x, mid in enumerate(middles) for u in mid}
    forbidden = {v ^ 256 for v in forced if (v & 127) != q}
    if forced & forbidden or not forced <= outer:
        raise ValueError("Forced ports contradict the specified crossing")
    optional = sorted(outer - forced - forbidden)
    cnf = Formula()
    chosen = {v: cnf.variable() for v in optional}
    eps = {v: cnf.variable() for v in sorted(forced | set(optional))}
    parity = cnf.variable()
    for v, e in eps.items():
        # A 193-vertex path has two endpoints of the same global parity.
        # The variable permits either parity.
        cnf.clauses.append([-e, parity if v.bit_count() % 2 else -parity])
        guard = []
        if v in chosen:
            cnf.clauses.append([-e, chosen[v]])
            guard = [-chosen[v]]
        base = sum(t in fixed for t in NEIGHBOURS[v])
        # Two optional opposite x-copies cannot both be chosen.
        ns = [chosen[t] for t in NEIGHBOURS[v] if t in chosen and t != (v ^ 256)]
        bounds(cnf, ns, 1-base, 2-base, guard)
        bounds(cnf, ns, 0, 1-base, [-e])
        bounds(cnf, ns, 2-base, len(ns), guard + [e])
    for u in range(128):
        if u in chosen and u+256 in chosen:
            cnf.clauses.append([-chosen[u], -chosen[u+256]])
    for x in (0, 1):
        cnf.exactly([lit for v, lit in eps.items() if v >> 8 == x], 1)
    cnf.exactly(list(chosen.values()), 97-len(forced))
    return cnf, chosen, fixed


def extract(selected, middles, q):
    if len(selected) != 193:
        raise ValueError("Incorrect total")
    for x, mid in enumerate(middles):
        if {v & 127 for v in selected if v >> 7 == 1+2*x} != set(mid):
            raise ValueError("Middle vertex mismatch")
    if {v for v in selected if v < 256 and (v ^ 256) in selected} != {q}:
        raise ValueError("Incorrect crossing set")
    neighbours = {v: set(NEIGHBOURS[v]) & selected for v in selected}
    ends = sorted(v for v in selected if len(neighbours[v]) == 1)
    if (len(ends) != 2 or {v >> 8 for v in ends} != {0, 1}
            or any(len(neighbours[v]) != 2 for v in selected - set(ends))):
        raise ValueError("Degrees differ from the cube")
    groups = connected_parts(selected)
    if len(groups) > 1:
        cycles = [sorted(g) for g in groups if all(len(neighbours[v]) == 2 for v in g)]
        if not cycles:
            raise ValueError("Disconnected degree model without a cycle")
        return None, cycles
    path = [ends[0]]
    visited = set(path)
    while len(path) < 193:
        following = neighbours[path[-1]] - visited
        if len(following) != 1:
            raise ValueError("Could not extract path")
        path.append(following.pop())
        visited.add(path[-1])
    verify(path, False)
    return path, []


def solve(middles, q, cnf_path, seconds):
    cnf, chosen, fixed = encode(middles, q)
    attempts = []
    remaining = seconds
    while True:
        attempt = dict(cnf_sha256=cnf.save(cnf_path), variables=cnf.count, clauses=len(cnf.clauses))
        attempts.append(attempt)
        if remaining <= 0:
            attempt["outcome"] = "budget_exhausted"
            return dict(q=q, status="unknown", attempts=attempts)
        begin = monotonic()
        try:
            proc = subprocess.run([str(SOLVER), "-q", str(cnf_path)], capture_output=True, timeout=remaining)
        except subprocess.TimeoutExpired:
            attempt.update(outcome="timeout", seconds=monotonic()-begin)
            return dict(q=q, status="unknown", attempts=attempts)
        attempt["seconds"] = monotonic()-begin
        remaining -= attempt["seconds"]
        out = proc.stdout.decode("ascii", errors="replace")
        if proc.returncode == 20 and "s UNSATISFIABLE" in out:
            attempt["outcome"] = "UNSAT"
            return dict(q=q, status="native_exclusion", attempts=attempts)
        if proc.returncode != 10 or "s SATISFIABLE" not in out:
            raise RuntimeError((proc.returncode, out[-800:], proc.stderr[-400:]))
        model = {int(t) for line in out.splitlines() if line.startswith("v ")
                 for t in line.split()[1:] if int(t) > 0}
        selected = fixed | {v for v, lit in chosen.items() if lit in model}
        path, cycles = extract(selected, middles, q)
        if path is not None:
            attempt["outcome"] = "verified_192"
            return dict(q=q, status="witness", path=path, attempts=attempts)
        attempt.update(outcome="disjoint_cycles", cycles=cycles)
        for cycle in cycles:
            # Its cycle edges persist whenever all its vertices persist.
            cnf.clauses.append([-chosen[v] for v in cycle if v in chosen])


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=float, default=0.75, help="Solver wall time per crossing representative")
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error("Positive solver time required")
    source = (HERE / "middle.json").read_bytes()
    middles = json.loads(source)["layouts"][0]["middles"]
    for mid in middles:
        if len(mid) != 48 or any(not 0 <= v < 128 for v in mid):
            raise ValueError("Expected 47-edge Q7 middles")
        verify(mid, False)
    if set(middles[0]) & set(middles[1]):
        raise ValueError("Middles intersect")
    eligible = sorted(set(range(128)) - set(middles[0][1:-1]) - set(middles[1][1:-1]))
    axes = [8, 2, 16, 1, 4, 32, 64]
    perm = [22 ^ sum(mask for j, mask in enumerate(axes) if u & (1 << j)) for u in range(128)]
    for i in range(2):
        if [perm[v] for v in middles[i]] not in (middles[1-i], middles[1-i][::-1]):
            raise ValueError("Proposed face exchange does not preserve whole middle paths")
    if any(perm[perm[v]] != v for v in range(128)) or {perm[v] for v in eligible} != set(eligible):
        raise ValueError("Invalid crossing symmetry")
    orbits = sorted({tuple(sorted({q, perm[q]})) for q in eligible})
    rows = []
    record = dict(middles=middles, eligible_crossings=eligible, crossing_orbits=orbits,
                  face_exchange=dict(axis_images=axes, translation=22), solver_seconds_per_query=args.seconds,
                  solver_sha256=sha256(SOLVER.read_bytes()).hexdigest(),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  formula_source_sha256=sha256((SOURCE/"arc_sat.py").read_bytes()).hexdigest(),
                  verifier_source_sha256=sha256((SOURCE/"open_coil.py").read_bytes()).hexdigest(),
                  middle_sha256=sha256(source).hexdigest(), rows=rows)
    destination = HERE / "free-outer.json"
    with TemporaryDirectory(prefix="q9-free-outer-") as directory:
        for i, orbit in enumerate(orbits):
            row = solve(middles, orbit[0], Path(directory)/"outer.cnf", args.seconds)
            rows.append(dict(orbit=orbit, **row))
            record["remaining_orbits"] = orbits[i+1:]
            record["status_counts_by_orbit"] = dict(Counter(r["status"] for r in rows))
            temporary = destination.with_suffix(".tmp")
            temporary.write_text(json.dumps(record, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
            temporary.replace(destination)
            print("q", orbit, row["status"], "attempts", len(row["attempts"]), flush=True)
            if row["status"] == "witness":
                break


if __name__ == "__main__":
    main()
