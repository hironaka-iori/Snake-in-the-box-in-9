"""Search both ends simultaneously. Each connected model gives an explicit Q9 path."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import os
import subprocess
import time

from open_coil import ADJ, HERE, bits, rotations, verify, vertices


class Formula:
    def __init__(self):
        self.count = 0
        self.clauses = []

    def variable(self):
        self.count += 1
        return self.count

    def at_most(self, literals, maximum):
        if maximum < 0:
            self.clauses.append([])
            return
        if maximum >= len(literals):
            return
        def merge(values):
            if len(values) == 1:
                return values
            half = len(values) // 2
            left, right = merge(values[:half]), merge(values[half:])
            out = [self.variable() for _ in range(min(maximum + 1, len(values)))]
            for i in range(len(left) + 1):
                for j in range(len(right) + 1):
                    if 0 < i+j <= len(out):
                        clause = ([-left[i-1]] if i else []) + ([-right[j-1]] if j else [])
                        self.clauses.append(clause + [out[i+j-1]])
            return out
        self.clauses.append([-merge(literals)[maximum]])

    def exactly(self, xs, n):
        self.at_most(xs, n)
        self.at_most([-x for x in xs], len(xs)-n)

    def save(self, path):
        data = f"p cnf {self.count} {len(self.clauses)}\n" + "".join(
            " ".join(map(str, c)) + " 0\n" for c in self.clauses)
        path.write_bytes(data.encode("ascii"))
        return sha256(data.encode("ascii")).hexdigest()


def encode(spine):
    fixed = bits(spine)
    ends = {spine[0], spine[-1]}
    # Further selected vertices may touch at most one spine endpoint
    # except that a common neighbour of both endpoints would close the
    # entire spine into a cycle and is impossible in a connected path.
    allowed = {v for v in range(512) if not (1 << v) & fixed and
               (not (ADJ[v] & fixed) or (ADJ[v] & fixed) in {1 << e for e in ends})}
    stack = list(ends)
    seen = set(stack)
    while stack:
        v = stack.pop()
        following = {u for u in vertices(ADJ[v]) if u in allowed and u not in seen}
        seen.update(following)
        stack.extend(following)
    allowed = sorted(seen - ends)
    cnf = Formula()
    chosen = {v: cnf.variable() for v in allowed}
    eps = {v: cnf.variable() for v in sorted(set(allowed) | ends)}
    for v, e in eps.items():
        prefix = [] if v in ends else [-chosen[v]]
        if prefix:
            cnf.clauses.append([-e, chosen[v]])
        baseline = (ADJ[v] & fixed).bit_count()
        ns = [chosen[u] for u in vertices(ADJ[v]) if u in chosen]
        for group in combinations(ns, 3-baseline):
            cnf.clauses.append(prefix + [-i for i in group])
        for group in combinations(ns, 2-baseline):
            cnf.clauses.append([-e] + [-i for i in group])
        if baseline == 0:
            cnf.clauses.append(prefix + ns)
            for i in ns:
                cnf.clauses.append(prefix + [e, -i] + [j for j in ns if i != j])
        elif baseline == 1:
            cnf.clauses.append(prefix + [e] + ns)
    cnf.exactly(list(eps.values()), 2)
    cnf.exactly(list(chosen.values()), 193 - len(spine))
    return cnf, chosen


def connected_parts(selected):
    remaining = set(selected)
    components = []
    while remaining:
        queue = [remaining.pop()]
        for v in queue:
            ns = remaining.intersection(vertices(ADJ[v]))
            remaining.difference_update(ns)
            queue.extend(ns)
        components.append(queue)
    return components


def solve(spine, executable, cnf_path, seconds):
    cnf, chosen = encode(spine)
    before = time.monotonic()
    attempts = []
    while True:
        digest = cnf.save(cnf_path)
        allowance = seconds - (time.monotonic() - before)
        if allowance <= 0:
            return dict(status="unfinished", attempts=attempts)
        try:
            p = subprocess.run([str(executable), "-q", str(cnf_path)], capture_output=True,
                               timeout=allowance)
        except subprocess.TimeoutExpired:
            attempts.append(dict(cnf=digest, outcome="timed_out"))
            return dict(status="unfinished", attempts=attempts)
        output = p.stdout.decode("ascii", errors="replace")
        if p.returncode == 20 and "s UNSATISFIABLE" in output:
            attempts.append(dict(cnf=digest, outcome="UNSAT"))
            return dict(status="native_exclusion", attempts=attempts)
        if p.returncode != 10 or "s SATISFIABLE" not in output:
            raise RuntimeError((p.returncode, output[-1000:], p.stderr[-500:]))
        model = {int(v) for line in output.splitlines() if line.startswith("v ")
                 for v in line.split()[1:] if int(v)>0}
        sel = set(spine) | {v for v, i in chosen.items() if i in model}
        if len(sel) != 193:
            raise ValueError("Cardinality")
        neighbours = {v: set(vertices(ADJ[v])).intersection(sel) for v in sel}
        if sorted(map(len, neighbours.values())) != [1,1]+[2]*191:
            raise ValueError("Degree")
        groups = connected_parts(sel)
        if len(groups) == 1:
            path = [next(v for v in sel if len(neighbours[v]) == 1)]
            while len(path) < 193:
                onward = neighbours[path[-1]].difference(path[-2:])
                if len(onward) != 1:
                    raise ValueError("Path extraction")
                path.append(onward.pop())
            verify(path, False)
            attempts.append(dict(cnf=digest, outcome="verified_192"))
            return dict(status="witness", path=path, attempts=attempts)
        cycles = [sorted(c) for c in groups if all(len(neighbours[v]) == 2 for v in c)]
        if not cycles:
            raise ValueError("Disconnected degree model without a cycle")
        attempts.append(dict(cnf=digest, outcome="cycles", vertices=cycles))
        for cycle in cycles:
            cnf.clauses.append([-chosen[v] for v in cycle if v in chosen])


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("spine", type=int)
    cli.add_argument("seconds", type=float)
    cli.add_argument("--resume-dfs", type=Path)
    args = cli.parse_args()
    data = json.loads((HERE / "coil9.json").read_bytes())
    coil = data["q9_rows"][0]["vertices"]
    verify(coil, True)
    executable = Path("D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe")
    syms = rotations(coil)
    starts = set(range(len(coil)))
    prior_hash = None
    if args.resume_dfs:
        prior = json.loads(args.resume_dfs.read_bytes())
        if prior["spine"] != args.spine or prior["coil_sha256"] != sha256((HERE/"coil9.json").read_bytes()).hexdigest():
            raise ValueError("Wrong DFS input")
        prior_hash = sha256(args.resume_dfs.read_bytes()).hexdigest()
        starts -= {i for r in prior["rows"] if r["status"] == "excluded" for i in r["orbit"]}
    dest = HERE / f"sat-{args.spine}-{args.seconds:g}.json"
    pins = dict(spine=args.spine, seconds_per_query=args.seconds, prior_dfs_sha256=prior_hash,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                solver_sha256=sha256(executable.read_bytes()).hexdigest(),
                coil_sha256=sha256((HERE/"coil9.json").read_bytes()).hexdigest())
    rows = []
    if dest.exists():
        saved = json.loads(dest.read_bytes())
        if any(saved[key] != value for key, value in pins.items()):
            raise ValueError("Prior query inputs differ")
        rows = saved["rows"]
        for row in rows:
            starts.difference_update(row["orbit"])
        if any(r["status"] == "witness" for r in rows):
            return
    with TemporaryDirectory(prefix="q9-coil-") as tmp:
        while starts:
            first = min(starts)
            orbit = sorted({(off + sign*first - (args.spine-1 if sign < 0 else 0)) % 192 for off, sign in syms})
            if not set(orbit) <= starts:
                raise ValueError("Inconsistent orbit")
            starts.difference_update(orbit)
            spine = [coil[(first+j)%192] for j in range(args.spine)]
            result = solve(spine, executable, Path(tmp)/"arc.cnf", args.seconds)
            rows.append(dict(start=first, orbit=orbit, **result))
            tmpfile = dest.with_suffix(".tmp")
            tmpfile.write_text(json.dumps(dict(**pins, rows=rows, remaining_starts=sorted(starts)),
                                          indent=2)+"\n", encoding="utf-8",newline="\n")
            os.replace(tmpfile, dest)
            if result["status"] == "witness":
                break
    print(args.spine, "orbits", len(rows), dict(Counter(r["status"] for r in rows)))


if __name__ == "__main__":
    main()
