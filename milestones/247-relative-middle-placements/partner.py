"""Search the whole rooted Q8 complement of each published 96-edge arm."""
from argparse import ArgumentParser
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import gzip
import json
import subprocess
import sys


HERE = Path(__file__).resolve().parent
PREV = HERE.parent / "246-eight-dimensional-parents"
sys.path.insert(0, str(PREV))
from free_outer import Formula, SOLVER, SOURCE, bounds


NEIGHBOURS = [tuple(v ^ (1 << i) for i in range(8)) for v in range(256)]


def digest(path):
    h = sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def verify(path, dimension):
    if len(path) != len(set(path)) or any(not 0 <= v < 1 << dimension for v in path):
        raise ValueError("Out-of-range or repeated vertex")
    for i, u in enumerate(path):
        for j in range(i + 1, len(path)):
            if ((u ^ path[j]).bit_count() == 1) != (j == i + 1):
                raise ValueError(("Bad induced adjacency", i, j))


def parent_arms():
    labels = json.loads((PREV / "arm-structure.json").read_bytes())["long_class_ids"]
    pairs = json.loads((PREV / "comparison.json").read_bytes())["one_crossing_pairs"]
    return {i: next(p["long"] for p in pairs if p["seed"] == i) for i in labels}


def rooted_parent(path, endpoint):
    if endpoint not in (0, 1) or len(path) != 97:
        raise ValueError("Expected a 96-edge parent and a valid endpoint")
    oriented = path if endpoint == 0 else path[::-1]
    result = [x ^ oriented[0] for x in oriented]
    verify(result, 8)
    return result


def validate_prefix(parent, prefix):
    if not prefix or prefix[0] != 0 or len(prefix) > 96 or set(parent) & set(prefix) != {0}:
        raise ValueError("Illegal rooted prefix")
    verify(prefix, 8)


def next_vertices(parent, prefix):
    """All admissible next steps, in normalized Q8 vertex numbers."""
    validate_prefix(parent, prefix)
    if len(prefix) == 96:
        return []
    return [v for v in NEIGHBOURS[prefix[-1]] if v not in parent and v not in prefix and
            all((v ^ u).bit_count() > 1 for u in prefix[:-1])]


def face_bounds(cnf, chosen):
    for dimension, cap in ((2, 3), (3, 5)):
        for axes in combinations(range(8), dimension):
            offsets = [0]
            for axis in axes:
                offsets += [x | (1 << axis) for x in offsets]
            mask = offsets[-1]
            for low in range(256):
                if low & mask:
                    continue
                local = [chosen[low | offset] for offset in offsets if (low | offset) in chosen]
                for group in combinations(local, cap + 1):
                    cnf.clauses.append([-lit for lit in group])


def cycle_clause(chosen, vertices):
    seen = set(vertices)
    if len(seen) != len(vertices) or not seen or not seen <= set(chosen):
        raise ValueError("Bad cycle-cut vertices")
    if any(len(seen.intersection(NEIGHBOURS[v])) != 2 for v in seen):
        raise ValueError("Invalid cycle-cut degrees")
    reached = {next(iter(seen))}
    stack = list(reached)
    while stack:
        extra = seen.intersection(NEIGHBOURS[stack.pop()]) - reached
        reached.update(extra)
        stack.extend(extra)
    if reached != seen:
        raise ValueError("Disconnected cycle-cut vertices")
    return [-chosen[v] for v in sorted(seen)]


def encode(parent, prefix=(0,), cycles=()):
    validate_prefix(parent, prefix)
    if parent[0] != 0:
        raise ValueError("Joining endpoint has not been normalized")
    cnf = Formula()
    allowed = sorted(set(range(256)) - set(parent[1:]))
    chosen = {v: cnf.variable() for v in allowed}
    ends = {v: cnf.variable() for v in allowed if v.bit_count() % 2}
    cnf.exactly(list(ends.values()), 1)
    for parity in (0, 1):
        cnf.exactly([chosen[v] for v in allowed if v.bit_count() % 2 == parity], 48)
    for v, lit in chosen.items():
        ns = [chosen[u] for u in NEIGHBOURS[v] if u in chosen]
        if v == 0:
            bounds(cnf, ns, 1, 1, [])
        elif v not in ends:
            bounds(cnf, ns, 2, 2, [-lit])
        else:
            e = ends[v]
            cnf.clauses.append([-e, lit])
            bounds(cnf, ns, 1, 2, [-lit])
            bounds(cnf, ns, 0, 1, [-e])
            bounds(cnf, ns, 2, len(ns), [-lit, e])
    cnf.clauses.extend([chosen[v]] for v in prefix)
    for i, v in enumerate(prefix):
        if v in ends and i < 95:
            cnf.clauses.append([-ends[v]])
        if i + 1 < len(prefix):
            required = {prefix[i+1]}
            if i:
                required.add(prefix[i-1])
            cnf.clauses.extend([-chosen[u]] for u in NEIGHBOURS[v] if u in chosen and u not in required)
    face_bounds(cnf, chosen)
    for cycle in cycles:
        cnf.clauses.append(cycle_clause(chosen, cycle))
    return cnf, chosen


def extract(parent, prefix, selected):
    if len(selected) != 96 or sum(v.bit_count() % 2 for v in selected) != 48:
        raise ValueError("Incorrect partner parity quotas")
    if set(parent) & selected != {0} or not set(prefix) <= selected:
        raise ValueError("Incorrect root, prefix or parent avoidance")
    adj = {v: selected.intersection(NEIGHBOURS[v]) for v in selected}
    ends = {v for v, ns in adj.items() if len(ns) == 1}
    if len(ends) != 2 or 0 not in ends or not next(v for v in ends if v).bit_count() % 2:
        raise ValueError("Incorrect endpoints")
    if any(len(adj[v]) != 2 for v in selected - ends):
        raise ValueError("Incorrect internal degree")
    path = [0]
    while True:
        onward = adj[path[-1]] - ({path[-2]} if len(path) > 1 else set())
        if not onward:
            break
        if len(onward) != 1 or next(iter(onward)) in path:
            raise ValueError("Broken endpoint component")
        path.append(next(iter(onward)))
    if path[:len(prefix)] != list(prefix):
        raise ValueError("Selected path does not begin with prescribed prefix")
    remaining = selected - set(path)
    cycles = []
    while remaining:
        reached = {next(iter(remaining))}
        stack = list(reached)
        while stack:
            extra = adj[stack.pop()] - reached
            reached.update(extra)
            stack.extend(extra)
        cycles.append(sorted(reached))
        remaining -= reached
    if cycles:
        return None, None, sorted(cycles)
    lift = parent[::-1] + [256 + v for v in path]
    verify(path, 8)
    verify(lift, 9)
    if len(lift) != 193:
        raise ValueError("Joined witness has wrong length")
    return path, lift, []


def archive(source, kind):
    raw_hash = digest(source)
    if not source.stat().st_size:
        raise ValueError("Empty certificate artifact")
    directory = HERE / "partner-proofs"
    directory.mkdir(exist_ok=True)
    destination = directory / (raw_hash + "." + kind + ".gz")
    if not destination.exists():
        tmp = destination.with_suffix(".tmp")
        with source.open("rb") as src, tmp.open("wb") as raw:
            with gzip.GzipFile(filename="", mode="wb", fileobj=raw, compresslevel=1, mtime=0) as out:
                for block in iter(lambda: src.read(65536), b""):
                    out.write(block)
        tmp.replace(destination)
    return dict(file=destination.relative_to(HERE).as_posix(), sha256=raw_hash,
                gzip_sha256=digest(destination), bytes=source.stat().st_size)


def decide(parent, prefix, folder, seconds=2, seed=0, previous_cycles=()):
    """Solve one rooted normalized parent/prefix. A timeout leaves the case open."""
    cnf, chosen = encode(parent, prefix, previous_cycles)
    model_file, proof = folder / "model.cnf", folder / "proof.lrat"
    attempts = []
    answer = dict(prefix=list(prefix), initial_cycles=list(previous_cycles), seed=seed,
                  budget_seconds=seconds, status="unknown", attempts=attempts)
    remaining = seconds
    while remaining > 0:
        if proof.exists():
            proof.unlink()
        step = dict(cnf_sha256=cnf.save(model_file), variables=cnf.count, clauses=len(cnf.clauses))
        attempts.append(step)
        cmd = [str(SOLVER), "-q", "--seed="+str(seed), "--lrat", "--no-binary", str(model_file), str(proof)]
        begin = monotonic()
        try:
            result = subprocess.run(cmd, capture_output=True, timeout=remaining)
        except subprocess.TimeoutExpired:
            step.update(result="timeout", seconds=monotonic()-begin)
            return answer
        elapsed = monotonic()-begin
        remaining -= elapsed
        step["seconds"] = elapsed
        if result.returncode == 20 and b"s UNSATISFIABLE" in result.stdout:
            answer.update(status="solver_unsat", cnf=archive(model_file, "cnf"), lrat=archive(proof, "lrat"))
            step["result"] = "UNSAT"
            return answer
        if result.returncode != 10 or b"s SATISFIABLE" not in result.stdout:
            raise RuntimeError((result.returncode, result.stdout[-300:], result.stderr[-300:]))
        true_lits = {int(s) for line in result.stdout.splitlines() if line.startswith(b"v ")
                     for s in line.split()[1:] if int(s) > 0}
        selected = {v for v, lit in chosen.items() if lit in true_lits}
        partner, path, cycles = extract(parent, prefix, selected)
        if path is not None:
            answer.update(status="witness", partner=partner, q9_path=path,
                          verified_pairs=dict(parent=4656, partner=4560, joined=18528))
            step["result"] = "connected"
            return answer
        step.update(result="disconnected", cycles=cycles)
        for cycle in cycles:
            cnf.clauses.append(cycle_clause(chosen, cycle))
    return answer


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--seconds", type=float, default=2)
    cli.add_argument("--seed", type=int, default=0)
    cli.add_argument("--class-id", type=int)
    cli.add_argument("--endpoint", type=int, choices=[0, 1])
    cli.add_argument("--prefix", type=int, nargs="+", default=[0], help="Normalized ordered Q8 vertices from zero")
    cli.add_argument("--split-next", action="store_true", help="Query every admissible next step of the prefix")
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    arms = parent_arms()
    if args.seconds <= 0 or args.seed < 0 or (args.class_id is not None and args.class_id not in arms):
        cli.error("Invalid solver budget, seed, or arm")
    if args.prefix != [0] and (args.class_id is None or args.endpoint is None):
        cli.error("A nontrivial normalized prefix must identify its arm and joining endpoint")
    solver_pin = json.loads((PREV / "ceiling.json").read_bytes())["pins"]["cadical.exe"]
    if digest(SOLVER) != solver_pin:
        raise ValueError("Pinned solver differs")
    files = (Path(__file__), PREV/"arm-structure.json", PREV/"comparison.json", PREV/"free_outer.py",
             SOURCE/"arc_sat.py", SOLVER)
    coverage = []
    selected_ids = sorted(arms) if args.class_id is None else [args.class_id]
    ends = [0, 1] if args.endpoint is None else [args.endpoint]
    for i in selected_ids:
        for end in ends:
            parent = rooted_parent(arms[i], end)
            validate_prefix(parent, args.prefix)
            children = next_vertices(parent, args.prefix)
            prefixes = [args.prefix]
            if args.split_next and len(args.prefix) < 96:
                prefixes = [args.prefix + [v] for v in children]
            coverage.append(dict(class_id=i, endpoint=end, rooted_parent=parent,
                                 next_vertices=children, requested_prefixes=prefixes))
    destination = args.output
    if destination is None:
        name = "partners" if args.class_id is None and args.endpoint is None and not args.split_next else (
            "partner-" + str(args.class_id) + "-" + str(args.endpoint) + "-" +
            "_".join(map(str, args.prefix)) + ("-children" if args.split_next else ""))
        destination = HERE / (name + ".json")
    jobs = sum(len(c["requested_prefixes"]) for c in coverage)
    rows = []
    record = dict(pins={p.name: digest(p) for p in files}, coverage=coverage, requested=jobs,
                  pending=jobs, records=rows, endpoints="0 first and 1 last vertex of the stored 96-edge arm",
                  domain="All rooted 95-edge induced Q8 partners avoiding the other 96 parent vertices.")
    def save():
        record["pending"] = jobs-len(rows)
        tmp = destination.with_suffix(".tmp")
        tmp.write_text(json.dumps(record, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
        tmp.replace(destination)
    save()
    with TemporaryDirectory(prefix="q8-rooted-partner-") as temporary:
        for case in coverage:
            for prefix in case["requested_prefixes"]:
                result = decide(case["rooted_parent"], prefix, Path(temporary), args.seconds, args.seed)
                rows.append(dict(class_id=case["class_id"], endpoint=case["endpoint"], **result))
                save()
                print("Arm", case["class_id"], "endpoint", case["endpoint"], "prefix", prefix,
                      result["status"], flush=True)
                if result["status"] == "witness":
                    return


if __name__ == "__main__":
    main()
