"""Search every ordered pair of arm lengths <=98 with sum >=191."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import gzip
import json
import subprocess

from free_outer import HERE, SOURCE, SOLVER, Formula, NEIGHBOURS, bounds, connected_parts, verify
from refine_outer import forbid_short_cycles


def template(middles, q):
    possible = {v+256*x for x, mid in enumerate(middles) for v in range(128) if v not in mid[1:-1]}
    ports = {u+256*x for x, mid in enumerate(middles) for u in (q, mid[0], mid[-1])}
    fixed = ports | {128+256*x+u for x, mid in enumerate(middles) for u in mid}
    forbidden = {v ^ 256 for v in ports if (v & 127) != q}
    if ports & forbidden or not ports <= possible:
        raise ValueError("Inconsistent crossing")
    cnf = Formula()
    chosen = {v: cnf.variable() for v in sorted(possible - ports - forbidden)}
    ends = {v: cnf.variable() for v in sorted(set(chosen) | ports)}
    for v, end in ends.items():
        guard = []
        if v in chosen:
            cnf.clauses.append([-end, chosen[v]])
            guard = [-chosen[v]]
        baseline = sum(t in fixed for t in NEIGHBOURS[v])
        ns = [chosen[t] for t in NEIGHBOURS[v] if t in chosen and t != (v ^ 256)]
        bounds(cnf, ns, 1-baseline, 2-baseline, guard)
        bounds(cnf, ns, 0, 1-baseline, [-end])
        bounds(cnf, ns, 2-baseline, len(ns), guard + [end])
    for u in range(128):
        if u in chosen and (u+256) in chosen:
            cnf.clauses.append([-chosen[u], -chosen[u+256]])
    for x in (0, 1):
        cnf.exactly([value for v, value in ends.items() if v >> 8 == x], 1)
    forbid_short_cycles(cnf, chosen, fixed)
    return cnf, chosen, fixed, ends


def encode(middles, q, a, b, base=None):
    """Recreate a case, before applying any later cycle cuts."""
    shared, chosen, fixed, ends = template(middles, q) if base is None else base
    cnf = Formula()
    cnf.count = shared.count
    cnf.clauses = shared.clauses.copy()
    root_parity = q.bit_count() % 2
    for x, length in enumerate((a, b)):
        outer_count = length - 47
        end_parity = (root_parity + length) % 2
        for v, lit in ends.items():
            if v >> 8 == x and (v & 127).bit_count() % 2 != end_parity:
                cnf.clauses.append([-lit])
        for parity in (0, 1):
            def in_group(v):
                return v >> 7 == 2*x and (v & 127).bit_count() % 2 == parity
            quota = outer_count // 2 + int(outer_count % 2 and parity == root_parity)
            quota -= sum(in_group(v) for v in fixed)
            cnf.exactly([lit for v, lit in chosen.items() if in_group(v)], quota)
    return cnf, chosen, fixed


def inspect(selected, middles, q, a, b):
    for x, length in enumerate((a, b)):
        if sum(v >> 8 == x for v in selected) != length+1:
            raise ValueError("Incorrect arm cardinality")
        if {v & 127 for v in selected if v >> 7 == 1+2*x} != set(middles[x]):
            raise ValueError("Incorrect middle")
    if {v for v in selected if v < 256 and v+256 in selected} != {q}:
        raise ValueError("Incorrect shared projection")
    adj = {v: set(NEIGHBOURS[v]) & selected for v in selected}
    ends = sorted(v for v in selected if len(adj[v]) == 1)
    if (len(ends) != 2 or {v >> 8 for v in ends} != {0, 1}
            or any(len(adj[v]) != 2 for v in selected - set(ends))):
        raise ValueError("Incorrect induced degrees")
    for v in ends:
        if (v & 128) or ((v & 127).bit_count() - q.bit_count() - (a, b)[v >> 8]) % 2:
            raise ValueError("Incorrect outer endpoint")
    groups = connected_parts(selected)
    if len(groups) > 1:
        cycles = [sorted(g) for g in groups if all(len(adj[v]) == 2 for v in g)]
        if not cycles:
            raise ValueError("Disconnected model without a cycle")
        return None, cycles
    path = [ends[0]]
    visited = set(path)
    while len(path) < len(selected):
        nxt = adj[path[-1]] - visited
        if len(nxt) != 1:
            raise ValueError("Cannot reconstruct path")
        path.append(nxt.pop())
        visited.add(path[-1])
    verify(path, False)
    return path, []


def archive(proof, name):
    output = HERE / "ceiling-proofs"
    output.mkdir(exist_ok=True)
    target = output / (name+".lrat.gz")
    digest = sha256()
    with proof.open("rb") as src, target.open("wb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0, compresslevel=1) as dst:
            for chunk in iter(lambda: src.read(65536), b""):
                digest.update(chunk)
                dst.write(chunk)
    return dict(lrat=str(target.relative_to(HERE).as_posix()), lrat_sha256=digest.hexdigest(),
                lrat_bytes=proof.stat().st_size)


def decide(middles, q, a, b, base, folder, seconds, *, pinned=None, seed=0, previous=()):
    cnf, chosen, fixed = encode(middles, q, a, b, base)
    if pinned is not None:
        if not fixed <= pinned or not pinned <= fixed | set(chosen):
            raise ValueError("Control outside the construction family")
        cnf.clauses.extend([lit if v in pinned else -lit] for v, lit in chosen.items())
    for entry in previous:
        for cycle in entry.get("cycles", []):
            cnf.clauses.append([-chosen[v] for v in cycle if v in chosen])
    formula, proof = folder / "model.cnf", folder / "proof.lrat"
    attempts = list(previous)
    remaining = seconds
    while remaining > 0:
        if proof.exists():
            proof.unlink()
        entry = dict(cnf_sha256=cnf.save(formula), variables=cnf.count, clauses=len(cnf.clauses), seed=seed)
        attempts.append(entry)
        args = [str(SOLVER), "-q", "--seed="+str(seed), "--lrat", "--no-binary", str(formula), str(proof)]
        start = monotonic()
        try:
            proc = subprocess.run(args, capture_output=True, timeout=remaining)
        except subprocess.TimeoutExpired:
            entry.update(result="timeout", seconds=monotonic()-start)
            break
        entry["seconds"] = monotonic()-start
        remaining -= entry["seconds"]
        if proc.returncode == 20 and b"s UNSATISFIABLE" in proc.stdout:
            if pinned is not None:
                raise ValueError("The verified 191-edge selection failed its positive control")
            if not proof.is_file() or not proof.stat().st_size:
                raise ValueError("Missing text LRAT")
            entry.update(result="UNSAT", **archive(proof, f"q{q}-a{a}-b{b}"))
            return dict(q=q, a=a, b=b, status="native_exclusion", attempts=attempts)
        if proc.returncode != 10 or b"s SATISFIABLE" not in proc.stdout:
            raise RuntimeError((proc.returncode, proc.stdout[-500:], proc.stderr[-500:]))
        model = {int(s) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                 for s in line.split()[1:] if int(s)>0}
        selected = fixed | {v for v, lit in chosen.items() if lit in model}
        if pinned is not None and selected != pinned:
            raise ValueError("Control vertex set changed")
        path, cycles = inspect(selected, middles, q, a, b)
        if path is not None:
            entry["result"] = "verified_path"
            return dict(q=q, a=a, b=b, status="witness", attempts=attempts, path=path)
        entry.update(result="disconnected", cycles=cycles)
        for cycle in cycles:
            cnf.clauses.append([-chosen[v] for v in cycle if v in chosen])
    return dict(q=q, a=a, b=b, status="unknown", attempts=attempts)


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--seconds", type=float, default=0.8)
    cli.add_argument("--retry-seconds", type=float, default=2.5)
    args = cli.parse_args()
    if args.seconds <= 0 or args.retry_seconds < 0:
        cli.error("Invalid solver time budget")
    middle_file = HERE / "middle.json"
    layout = json.loads(middle_file.read_bytes())["layouts"][0]
    middle, known = layout["middles"], layout["best"]
    verify(known, False)
    if len(known) != 192:
        raise ValueError("Expected a 191-edge control")
    for mid in middle:
        verify(mid, False)
        if len(mid) != 48 or any(v not in range(128) for v in mid):
            raise ValueError("Invalid Q7 middle")
    if set(middle[0]) & set(middle[1]):
        raise ValueError("Middles intersect")
    eligible = set(range(128))-set(middle[0][1:-1])-set(middle[1][1:-1])
    axes = [8, 2, 16, 1, 4, 32, 64]
    image = [22 ^ sum(mask for j, mask in enumerate(axes) if v & (1<<j)) for v in range(128)]
    if any(image[image[v]] != v for v in range(128)) or {image[v] for v in eligible} != eligible:
        raise ValueError("Invalid involution")
    for x in (0, 1):
        if [image[v] for v in middle[x]] not in (middle[1-x], middle[1-x][::-1]):
            raise ValueError("Invalid middle exchange")
    orbits = sorted({tuple(sorted((q, image[q]))) for q in eligible})
    lengths = [(a,b) for a in range(93,99) for b in range(93,99) if a+b>=191]
    cases = {}
    files = [Path(__file__), HERE/"refine_outer.py", HERE/"free_outer.py", SOURCE/"arc_sat.py",
             SOURCE/"open_coil.py", middle_file, SOLVER]
    record = dict(pins={f.name:sha256(f.read_bytes()).hexdigest() for f in files}, middles=middle,
                  crossing_orbits=orbits, mate_exchanges_arm_lengths=True, lengths=lengths,
                  seconds=args.seconds, retry_seconds=args.retry_seconds)
    dest = HERE / "ceiling.json"
    def save():
        rows = list(cases.values())
        record.update(records=rows, remaining=len(orbits)*len(lengths)-len(rows),
                      outcomes=dict(Counter(row["status"] for row in rows)))
        temp = dest.with_suffix(".tmp")
        temp.write_text(json.dumps(record,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
        temp.replace(dest)
    with TemporaryDirectory(prefix="q9-pair-ceiling-") as directory:
        folder = Path(directory)
        sel = set(known)
        qs = {v for v in sel if v < 256 and v+256 in sel}
        if len(qs) != 1:
            raise ValueError("Missing control crossing")
        q = qs.pop()
        control = decide(middle, q, sum(v<256 for v in sel)-1, sum(v>=256 for v in sel)-1,
                         template(middle,q), folder, 10, pinned=sel)
        if control["status"] != "witness":
            raise ValueError("No positive control result")
        record["positive_control"] = control
        save()
        for seed, budget in ((0,args.seconds),(1,args.retry_seconds)):
            if budget <= 0:
                continue
            for orbit in orbits:
                q = orbit[0]
                pending = [(a,b) for a,b in lengths if (q,a,b) not in cases or cases[q,a,b]["status"]=="unknown"]
                if not pending:
                    continue
                base = template(middle,q)
                for a,b in pending:
                    earlier = cases.get((q,a,b),{}).get("attempts",[])
                    row = decide(middle,q,a,b,base,folder,budget,seed=seed,previous=earlier)
                    cases[q,a,b] = row
                    if row["status"] == "witness":
                        save()
                        print("Verified path",len(row["path"])-1,q,a,b,flush=True)
                        return
                save()
                print("pass",seed,"q",q,record["outcomes"],flush=True)


if __name__ == "__main__":
    main()
