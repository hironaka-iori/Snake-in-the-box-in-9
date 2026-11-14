"""Reconstruct the projection and its distance bounds, then verify a DRAT proof."""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import subprocess
from consistent_design import distance_network
from rerun_deep_certificate import digest
from solve import model, paths, save
from verify_distances import check_table


def certify(case, checker):
    row, = json.loads(case.read_text())
    assert row["search"]["status"] == "UNSAT"
    bits = row["bits"]
    families = row["cliques"]
    target = paths()[1]
    table, _ = distance_network(target, bits)
    passes = check_table(target, bits, table, families)
    name = "triproof-" + "".join(map(str,bits))
    prefix = Path(name)
    result = model(target, bits, certificate=prefix, strengthened=True,
                   distance_table=table, anchor_families=families)
    assert result["status"] == "UNSAT"
    cnf = prefix.with_suffix(".cnf")
    proof = prefix.with_suffix(".drat")
    core = prefix.with_suffix(".core")
    first = subprocess.run([str(checker), str(cnf), str(proof), "-l", str(core)],
                           check=True, capture_output=True)
    assert b"s VERIFIED" in first.stdout.splitlines()
    second = subprocess.run([str(checker), str(cnf), str(core)],
                            check=True, capture_output=True)
    assert b"s VERIFIED" in second.stdout.splitlines()
    for f in (cnf, core):
        with f.open("rb") as src, Path(str(f)+".gz").open("wb") as dst:
            with gzip.GzipFile(filename="", mode="wb", fileobj=dst, mtime=0) as gz:
                shutil.copyfileobj(src, gz)
    receipt = dict(bits=bits, retained=sorted(set(range(9))-set(bits)), runs=len(table),
                   families=families, independent_distance_passes=passes,
                   cnf_sha256=digest(cnf), core_sha256=digest(core),
                   core_compressed_bytes=Path(str(core)+".gz").stat().st_size,
                   checked=second.stdout.decode(errors="replace").splitlines()[-6:],
                   search=result)
    save(prefix.with_suffix(".json"), receipt)
    print(name, receipt["core_compressed_bytes"], receipt["checked"], flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("case", type=Path)
    parser.add_argument("--checker", type=Path, required=True)
    args = parser.parse_args()
    certify(args.case, args.checker.resolve())
