"""Enumerate long induced paths in Q7 outside the fixed first middle."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import gzip
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "246-eight-dimensional-parents"
sys.path.insert(0, str(PREVIOUS))
from free_outer import Formula, SOLVER, SOURCE, bounds, verify
from refine_outer import forbid_short_cycles

NEIGHBOURS = [tuple(v ^ (1 << j) for j in range(7)) for v in range(128)]
CASES = [(n, p) for n in (48, 49, 50, 47) for p in ((None,) if n % 2 else (0, 1))]


def encode(first, length, majority, blocks=()):
    """Regenerate DIMACS before or after a specified sequence of vertex-set cuts."""
    if (length, majority) not in CASES:
        raise ValueError("Incorrect length or majority parity")
    allowed = sorted(set(range(128))-set(first))
    cnf = Formula()
    chosen = {v: cnf.variable() for v in allowed}
    ends = {v: cnf.variable() for v in allowed}
    for v in allowed:
        sel, end = chosen[v], ends[v]
        adjacent = [chosen[u] for u in NEIGHBOURS[v] if u in chosen]
        cnf.clauses.append([-end, sel])
        bounds(cnf, adjacent, 1, 2, [-sel])
        bounds(cnf, adjacent, 0, 1, [-end])
        bounds(cnf, adjacent, 2, len(adjacent), [-sel, end])
    for parity in (0, 1):
        group = [v for v in allowed if v.bit_count() % 2 == parity]
        quota = (length+1)//2 + int(parity == majority)
        cnf.exactly([chosen[v] for v in group], quota)
        cnf.exactly([ends[v] for v in group], 1 if majority is None else 2*int(parity == majority))
    forbid_short_cycles(cnf, chosen, set())
    for block in blocks:
        cnf.clauses.append([-chosen[v] for v in block["vertices"]])
    return cnf, chosen


def inspect(selected, length, majority):
    if len(selected) != length+1:
        raise ValueError("Incorrect size returned")
    for parity in (0, 1):
        if sum(v.bit_count()%2 == parity for v in selected) != (length+1)//2 + int(parity == majority):
            raise ValueError("Incorrect parity returned")
    adj = {v: set(NEIGHBOURS[v]) & selected for v in selected}
    ends = sorted(v for v, ns in adj.items() if len(ns) == 1)
    if len(ends) != 2 or any(len(adj[v]) != 2 for v in selected - set(ends)):
        raise ValueError("Incorrect induced degrees")
    path = [ends[0]]
    seen = set(path)
    while path[-1] != ends[1]:
        onward = adj[path[-1]] - seen
        if len(onward) != 1:
            raise ValueError("Invalid path component")
        path.append(onward.pop())
        seen.add(path[-1])
    if seen == selected:
        verify(path, False)
        return path, []
    others = selected - seen
    cycles = []
    while others:
        start = min(others)
        component = [start]
        others.remove(start)
        for v in component:
            new = sorted(others & adj[v])
            others.difference_update(new)
            component.extend(new)
        if any(len(adj[v]) != 2 for v in component):
            raise ValueError("Invalid cycle component")
        cycles.append(sorted(component))
    return None, cycles


def store_proof(proof, tag):
    dest = HERE / "complementary-proofs"
    dest.mkdir(exist_ok=True)
    target = dest / (tag+".lrat.gz")
    digest = sha256()
    with proof.open("rb") as source, target.open("wb") as stream:
        with gzip.GzipFile(filename="", fileobj=stream, mode="wb", compresslevel=1, mtime=0) as storage:
            for block in iter(lambda: source.read(65536), b""):
                digest.update(block)
                storage.write(block)
    return dict(lrat=target.relative_to(HERE).as_posix(), lrat_sha256=digest.hexdigest(),
                lrat_bytes=proof.stat().st_size)


def enumerate_case(first, length, majority, known, directory, query_seconds, case_seconds, path_limit):
    paths = sorted({tuple(min(p,p[::-1])) for p in known})
    seen = {frozenset(p) for p in paths}
    if len(seen) != len(paths):
        raise ValueError("Duplicate known path set")
    blocks = [dict(kind="path", vertices=sorted(p)) for p in paths]
    cnf, chosen = encode(first,length,majority,blocks)
    rows = []
    record = dict(length=length, majority=majority, paths=paths, blocks=blocks, attempts=rows)
    formula, proof = directory/"model.cnf", directory/"case.lrat"
    remaining = case_seconds
    seed = 0
    tag = f"length{length}-" + ("balanced" if majority is None else f"majority{majority}")
    while remaining > 0:
        if len(paths) >= path_limit:
            return dict(record, status="unknown_path_limit")
        if proof.exists():
            proof.unlink()
        entry = dict(cnf_sha256=cnf.save(formula), blocks_at_query=len(blocks),
                     variables=cnf.count, clauses=len(cnf.clauses), seed=seed)
        rows.append(entry)
        # Plain CDCL disables preprocessing that can require RAT rather than
        # positive ordered RUP hints. Acceptance is established by separate replay.
        command = [str(SOLVER), "--plain", "-q", "--seed="+str(seed), "--lrat", "--no-binary",
                   str(formula),str(proof)]
        started = monotonic()
        try:
            proc = subprocess.run(command,capture_output=True,timeout=min(query_seconds,remaining))
        except subprocess.TimeoutExpired:
            elapsed = monotonic()-started
            remaining -= elapsed
            entry.update(result="timeout", seconds=elapsed)
            seed += 1
            continue
        elapsed = monotonic()-started
        remaining -= elapsed
        entry["seconds"] = elapsed
        if proc.returncode == 20 and b"s UNSATISFIABLE" in proc.stdout:
            if not proof.is_file() or not proof.stat().st_size:
                raise ValueError("Missing LRAT")
            entry.update(result="UNSAT", **store_proof(proof, tag))
            return dict(record, status="native_exhaustion")
        if proc.returncode != 10 or b"s SATISFIABLE" not in proc.stdout:
            raise RuntimeError((proc.returncode, proc.stdout[-500:], proc.stderr[-500:]))
        positive = {int(s) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                    for s in line.split()[1:] if int(s)>0}
        selected = {v for v, lit in chosen.items() if lit in positive}
        path,cycles = inspect(selected,length,majority)
        if path is not None:
            key = frozenset(path)
            if key in seen:
                raise ValueError("Repeated blocked path")
            seen.add(key)
            paths.append(tuple(path))
            new_blocks = [dict(kind="path", vertices=sorted(path))]
            entry["result"] = "verified_path"
        else:
            new_blocks = [dict(kind="cycle", vertices=cycle) for cycle in cycles]
            entry["result"] = "disconnected"
        for block in new_blocks:
            # An induced path of this size cannot contain a whole cycle.
            # A full-length accepted path blocks exactly its own vertex set.
            cnf.clauses.append([-chosen[v] for v in block["vertices"]])
        blocks.extend(new_blocks)
    return dict(record, status="unknown_time_limit")


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--query-seconds", type=float, default=4.0)
    cli.add_argument("--case-seconds", type=float, default=24.0)
    cli.add_argument("--path-limit", type=int, default=100)
    args = cli.parse_args()
    if min(args.query_seconds,args.case_seconds,args.path_limit) <= 0:
        cli.error("Budgets must be positive")
    orbit = HERE / "orbit.json"
    data = json.loads(orbit.read_bytes())
    first, reference = data["first"], data["reference"]
    for p in (first,reference):
        verify(p,False)
        if len(p)!=48 or any(v not in range(128) for v in p):
            raise ValueError("Expected Q7 paths of length 47")
    if set(first)&set(reference):
        raise ValueError("The reference meets the excluded path")
    known = {case: {} for case in CASES}
    known[47,None][frozenset(reference)] = reference
    rows = []
    files = [Path(__file__),orbit,SOLVER,PREVIOUS/"free_outer.py",PREVIOUS/"refine_outer.py",
             SOURCE/"arc_sat.py",SOURCE/"open_coil.py"]
    result = dict(pins={p.name:sha256(p.read_bytes()).hexdigest() for p in files},
                  first=first, reference=reference, solver_options=["--plain","-q","--lrat","--no-binary"],
                  query_seconds=args.query_seconds,case_seconds=args.case_seconds,
                  path_limit=args.path_limit,records=rows)
    dest = HERE / "complementary.json"
    with TemporaryDirectory(prefix="q7-complement-") as temp:
        for case in CASES:
            length,majority = case
            row = enumerate_case(first,length,majority,list(known[case].values()),Path(temp),
                                 args.query_seconds,args.case_seconds,args.path_limit)
            rows.append(row)
            # Contiguous subpaths of a verified induced path are induced.
            # Reuse their explicit checked orders as known solutions in later cases.
            for parent in row["paths"]:
                for n,m in CASES:
                    if n>=length:
                        continue
                    for i in range(length-n+1):
                        path = list(parent[i:i+n+1])
                        if m is not None and path[0].bit_count()%2 != m:
                            continue
                        verify(path,False)
                        known[n,m][frozenset(path)] = path
            for old in rows:
                case_key = old["length"],old["majority"]
                enumerated = {frozenset(p) for p in old["paths"]}
                later = [p for key,p in known[case_key].items() if key not in enumerated]
                if later and old["status"] == "native_exhaustion":
                    raise ValueError("A longer verified path contradicts the earlier exhaustion")
                old["additional_verified_subpaths"] = later
            temporary = dest.with_suffix(".tmp")
            temporary.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
            temporary.replace(dest)
            print("length",length,"majority",majority,row["status"],"verified sets",len(row["paths"]),
                  "queries",len(row["attempts"]),flush=True)


if __name__ == "__main__":
    main()
