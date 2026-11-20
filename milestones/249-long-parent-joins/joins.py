"""Search complete rooted partner domains for the six additional Q8 parents."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LAST = HERE.parent / "248-rooted-arm-capacity"
sys.path.insert(0, str(LAST))
from survey import partner, save_json
from certify import archive
from endpoint94 import encode94
import opposite

INVENTORY = LAST / "parents.json"
CHECKER = partner.PREV / "VerifyLrat.cs"
COMPILER = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def inputs():
    inventory = json.loads(INVENTORY.read_bytes())
    original = partner.PREV / "donors.json"
    if partner.digest(original) != inventory["source_sha256"]:
        raise ValueError("Archived donor array has changed")
    bank = json.loads(original.read_bytes())["shapes"]
    parents = {}
    for index in inventory["remaining_96"]:
        row = next(r for r in inventory["rows"] if r["donor_index"] == index)
        if row["path"] != bank[index]["path"] or row["edges"] != 96:
            raise ValueError("Donor index or stored length differs")
        for end in (0, 1):
            parents[index, end] = partner.rooted_parent(row["path"], end)
    return parents


def encode(parent, length, prefix, cycles):
    if length == 95:
        return partner.encode(parent, prefix, cycles)
    if length == 94:
        return encode94(parent, prefix, cycles)
    return opposite.encode(parent, length, prefix, cycles)


def solve(parent, length, prefix, temp, exe, seconds, seed):
    cnf, chosen = encode(parent, length, prefix, [])
    formula, raw = temp / "input.cnf", temp / "trace.lrat"
    cycles, attempts = [], []
    until = monotonic() + seconds
    while monotonic() < until:
        cnf_hash = cnf.save(formula)
        raw.unlink(missing_ok=True)
        attempt = dict(cnf_sha256=cnf_hash, variables=cnf.count, clauses=len(cnf.clauses))
        attempts.append(attempt)
        try:
            result = subprocess.run([str(partner.SOLVER), "-q", "--seed="+str(seed), "--lrat",
                                     "--no-binary", str(formula), str(raw)], capture_output=True,
                                    timeout=max(0.01, until-monotonic()))
        except subprocess.TimeoutExpired:
            attempt["outcome"] = "timeout"
            break
        if result.returncode == 20 and b"s UNSATISFIABLE" in result.stdout:
            rebuilt, _ = encode(parent, length, prefix, cycles)
            if rebuilt.save(formula) != cnf_hash:
                raise ValueError("Rebuilt formula differs")
            proof = HERE / "proofs" / (cnf_hash + ".lrat.gz")
            proof.parent.mkdir(exist_ok=True)
            raw_hash = archive(raw, proof)
            check = subprocess.run([str(exe), str(formula), str(proof)], capture_output=True, timeout=90)
            if check.returncode or not check.stdout.startswith(b"VERIFIED UNSAT "):
                raise ValueError(("LRAT replay failed", check.stderr[-500:], check.stdout[-500:]))
            attempt["outcome"] = "verified_unsat"
            return dict(status="excluded", attempts=attempts, cycles=cycles, cnf_sha256=cnf_hash,
                        proof=proof.relative_to(HERE).as_posix(), raw_sha256=raw_hash,
                        gzip_sha256=partner.digest(proof), checker=check.stdout.decode().strip())
        if result.returncode != 10 or b"s SATISFIABLE" not in result.stdout:
            raise RuntimeError((result.returncode, result.stderr[-400:]))
        truth = {int(v) for line in result.stdout.splitlines() if line.startswith(b"v ")
                 for v in line.split()[1:] if int(v)>0}
        selected = {v for v,lit in chosen.items() if lit in truth}
        found, extra = opposite.extract(parent, length, prefix, selected)
        if found:
            attempt["outcome"] = "connected"
            return dict(status="witness", attempts=attempts, cycles=cycles, **found)
        attempt.update(outcome="disconnected", cycles=extra)
        for cycle in extra:
            cnf.clauses.append(partner.cycle_clause(chosen, cycle))
        cycles.extend(extra)
    return dict(status="open", attempts=attempts, cycles=cycles)


def frontier(parent, records):
    """Unresolved prefix leaves, checking every admissible next vertex on splitting."""
    excluded = {tuple(row["prefix"]) for row in records if row["status"]=="excluded"}
    attempted = {tuple(row["prefix"]) for row in records}
    def leaves(prefix):
        if prefix in excluded:
            return []
        if prefix not in attempted:
            return [prefix]
        return [p for v in partner.next_vertices(parent, prefix) for p in leaves((*prefix,v))]
    return leaves((0,))


def main():
    args = ArgumentParser(description=__doc__)
    args.add_argument("--length", type=int, default=95, choices=range(1,96))
    args.add_argument("--depth", type=int, default=0)
    args.add_argument("--seconds", type=float, default=8)
    args.add_argument("--total", type=float, default=145)
    args.add_argument("--ids", type=int, nargs="+")
    opts = args.parse_args()
    if not 0 <= opts.depth < opts.length or min(opts.seconds,opts.total)<=0:
        args.error("Invalid depth or time allocation")
    parents = inputs()
    files = [Path(__file__), INVENTORY, partner.PREV/"donors.json", LAST/"opposite.py",
             LAST/"endpoint94.py", LAST/"certify.py", Path(partner.__file__),
             partner.PREV/"free_outer.py", partner.SOURCE/"arc_sat.py", CHECKER, COMPILER, partner.SOLVER]
    pins = {p.name:partner.digest(p) for p in files}
    output = HERE / ("partners-"+str(opts.length)+".json")
    data = json.loads(output.read_bytes()) if output.exists() else dict(length=opts.length, pins=pins, records=[])
    if data["pins"] != pins:
        raise ValueError("Input evidence differs from the previous run")
    if opts.ids and set(opts.ids)-{i for i,_ in parents}:
        args.error("Unknown 96-edge donor")
    with TemporaryDirectory(prefix="snake249-") as temporary:
        temp = Path(temporary)
        exe = temp/"VerifyLrat.exe"
        subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(CHECKER)],
                       check=True, capture_output=True, timeout=60)
        until = monotonic()+opts.total
        for (i,e),parent in parents.items():
            if opts.ids and i not in opts.ids:
                continue
            rows = [r for r in data["records"] if r["donor"]==i and r["endpoint"]==e]
            if any(r["status"]=="witness" for r in rows):
                continue
            for prefix in frontier(parent, rows):
                if len(prefix)-1>opts.depth:
                    continue
                if monotonic()>=until:
                    return
                details = solve(parent, opts.length, prefix, temp, exe, min(opts.seconds,until-monotonic()), 1)
                data["records"].append(dict(donor=i, endpoint=e, prefix=list(prefix), **details))
                save_json(output, data)
                print(i,e,opts.length,list(prefix),details["status"],flush=True)
                if details["status"]=="witness":
                    break


if __name__ == "__main__":
    main()
