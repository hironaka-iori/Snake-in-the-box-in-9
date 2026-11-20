"""Search both roots of every new parent from the 84-edge core census."""
from argparse import ArgumentParser
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

import partners
from partners import HERE, COMPILER, CHECKER, joins, partner, save_json
from audit import check_cycle, file_hash, path_ok, verified_partner
from geometry import shape
from hashlib import sha256
import gzip


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--target", type=int, required=True, choices=(191, 192))
    cli.add_argument("--replay", action="store_true")
    args = cli.parse_args()
    source = HERE / "cores-84.json"
    ledger = HERE / f"extended-{args.target}.json"
    pins = {**partners.pins(), "core_census": partner.digest(source),
            "extended.py": partner.digest(Path(__file__))}
    data = json.loads(ledger.read_bytes()) if ledger.exists() else dict(pins=pins, records=[])
    if data["pins"] != pins:
        raise ValueError("Changed source or proof dependencies")
    saved = {(r["id"], r["end"]): r for r in data["records"]}
    if len(saved) != len(data["records"]):
        raise ValueError("Duplicate endpoint record")
    checked = []
    with TemporaryDirectory(prefix="snake250-core-") as folder:
        temp = Path(folder)
        exe = temp / "VerifyLrat.exe"
        subprocess.run([str(COMPILER), "/nologo", "/optimize+", "/out:"+str(exe), str(CHECKER)],
                       check=True, capture_output=True, timeout=60)
        for row in json.loads(source.read_bytes())["new_shapes"]:
            seq = row["path"]
            path_ok(seq, 8)
            if sha256(shape(seq)).hexdigest() != row["id"] or len(seq)-1 != row["edges"]:
                raise ValueError("Parent mismatch")
            for end, order in enumerate((seq, seq[::-1])):
                key = row["id"], end
                parent = [v ^ order[0] for v in order]
                n = args.target - len(seq)
                if not args.replay:
                    if key in saved and saved[key]["status"] != "open":
                        continue
                    case = dict(parent=parent, edges=len(parent)-1, old_cap=98)
                    result = partners.query(case, n, [0], temp, exe, 45)
                    saved[key] = dict(id=row["id"], end=end, root=order[0], length=n, **result)
                    data["records"] = list(saved.values())
                    save_json(ledger, data)
                    print(args.target, key, result["status"], flush=True)
                    continue
                r = saved[key]
                if r["length"] != n or r["root"] != order[0]:
                    raise ValueError("Mismatched length or joining endpoint")
                cnf, chosen = joins.encode(parent, n, [0], [])
                infile = temp / "verify.cnf"
                for i, step in enumerate(r["steps"]):
                    if (cnf.save(infile), len(cnf.clauses), cnf.count) != (
                            step["cnf"], step["clauses"], step["variables"]):
                        raise ValueError("Base formula or refinement mismatch")
                    last = i == len(r["steps"])-1
                    if last:
                        if step["outcome"] != r["status"]:
                            raise ValueError("Terminal result mismatch")
                    elif step["outcome"] == "cycles" and step["cycles"]:
                        cnf.clauses.extend(check_cycle(c, chosen) for c in step["cycles"])
                    else:
                        raise ValueError("Invalid cycle refinement")
                if r["status"] == "excluded":
                    proof = HERE / "proofs" / (step["cnf"] + ".lrat.gz")
                    if (file_hash(proof), file_hash(proof, gzip.open)) != (r["compressed"], r["raw"]):
                        raise ValueError("Trace digest mismatch")
                    replay = subprocess.run([str(exe), str(infile), str(proof)], check=True,
                                            capture_output=True, timeout=90).stdout.decode().strip()
                    if replay != r["replay"] or not replay.startswith("VERIFIED UNSAT "):
                        raise ValueError("Trace rejected")
                elif r["status"] == "witness":
                    verified_partner(parent, r, n)
                elif r["status"] != "open":
                    raise ValueError("Unknown outcome")
                checked.append(dict(id=row["id"], end=end, root=order[0], status=r["status"], length=n))
    if args.replay:
        if len(saved) != len(checked):
            raise ValueError("Extra query")
        save_json(HERE / f"extended-audit-{args.target}.json",
                  dict(ledger_sha256=partner.digest(ledger), endpoints=checked))


if __name__ == "__main__":
    main()
