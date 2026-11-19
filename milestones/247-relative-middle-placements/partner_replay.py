"""Reconstruct saved partner exclusions, verify their exact inputs and replay the LRAT."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import subprocess

from partner import HERE, PREV, digest, encode, parent_arms, rooted_parent


def inspect_archive(entry):
    p = HERE / entry["file"]
    if digest(p) != entry["gzip_sha256"]:
        raise ValueError(("Compressed artifact hash", p))
    h = sha256()
    size = 0
    with gzip.open(p, "rb") as f:
        for b in iter(lambda: f.read(65536), b""):
            h.update(b)
            size += len(b)
    if h.hexdigest() != entry["sha256"] or size != entry["bytes"]:
        raise ValueError(("Uncompressed artifact hash or length", p))
    return p


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path, default=HERE / "partners.json")
    args = parser.parse_args()
    research = json.loads(args.source.read_bytes())
    arms = parent_arms()
    compiler = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    checker = PREV / "VerifyLrat.cs"
    reports = []
    excluded = [r for r in research["records"] if r["status"] == "solver_unsat"]
    with TemporaryDirectory(prefix="partner-lrat-") as tmp:
        folder = Path(tmp)
        exe = folder / "VerifyLrat.exe"
        if excluded:
            subprocess.run([str(compiler), "/nologo", "/optimize+", "/out:"+str(exe), str(checker)],
                           check=True, capture_output=True, timeout=60)
        for row in excluded:
            parent = rooted_parent(arms[row["class_id"]], row["endpoint"])
            all_cycles = list(row["initial_cycles"])
            for step in row["attempts"][:-1]:
                all_cycles.extend(step.get("cycles", []))
            regenerated, _ = encode(parent, row["prefix"], all_cycles)
            cnf = folder / "case.cnf"
            actual = regenerated.save(cnf)
            if actual != row["cnf"]["sha256"] or actual != row["attempts"][-1]["cnf_sha256"]:
                raise ValueError("Regenerated formula differs")
            inspect_archive(row["cnf"])
            proof = inspect_archive(row["lrat"])
            proc = subprocess.run([str(exe), str(cnf), str(proof)], capture_output=True, timeout=60)
            out = proc.stdout.decode("ascii").strip()
            if proc.returncode != 0 or not out.startswith("VERIFIED UNSAT "):
                raise ValueError(("LRAT failure", row["class_id"], row["endpoint"], out, proc.stderr[-400:]))
            reports.append(dict(class_id=row["class_id"], endpoint=row["endpoint"], prefix=row["prefix"],
                                regenerated_cnf_sha256=actual, proof_sha256=row["lrat"]["sha256"],
                                checked_cycle_cuts=len(all_cycles), verifier=out))
        checker_exe = digest(exe) if excluded else None
    record = dict(source_file=args.source.name, source_sha256=digest(args.source), cases=reports,
                  solver_exclusions=len(excluded), verified=len(reports), checker_source_sha256=digest(checker),
                  compiler_sha256=digest(compiler), checker_executable_sha256=checker_exe)
    destination = args.source.with_name(args.source.stem+"-lrat.json")
    destination.write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8", newline="\n")
    print("Replayed", len(reports), "of", len(excluded), "solver exclusions")


if __name__ == "__main__":
    main()
