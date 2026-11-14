"""Generate and independently replay UNSAT proofs for entry 87's five-bit masks."""
import argparse
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from solve import model,paths,save,BANK_HASH


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--checker",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--retain",type=Path)
    args=p.parse_args()
    _,target=paths()
    checker=args.checker.resolve()
    data=dict(bank_sha256=BANK_HASH,checker_sha256=sha256(checker.read_bytes()).hexdigest(),cases=[])
    with TemporaryDirectory() as tmp:
        folder=args.retain or Path(tmp)
        folder.mkdir(exist_ok=True,parents=True)
        for bits in sorted(combinations(range(9),5),key=lambda b:(not (1 in b and 4 in b),b)):
            prefix=folder/("mask-"+"".join(map(str,bits)))
            result=model(target,bits,certificate=prefix)
            if result["status"]!="UNSAT":
                raise RuntimeError((bits,result))
            cnf=prefix.with_suffix(".cnf")
            proof=prefix.with_suffix(".drat")
            proc=subprocess.run([str(checker),str(cnf),str(proof)],capture_output=True)
            text=proc.stdout.decode(errors="replace")
            if proc.returncode or "s VERIFIED" not in text.splitlines():
                raise RuntimeError((bits,proc.returncode,text[-1200:]))
            data["cases"].append(dict(bits=bits,cnf_sha256=sha256(cnf.read_bytes()).hexdigest(),
                                      drat_sha256=sha256(proof.read_bytes()).hexdigest(),
                                      drat_bytes=proof.stat().st_size,verified=True))
            save(args.output,data)
            if args.retain is None:
                cnf.unlink(); proof.unlink()
            print("verified",bits,flush=True)


if __name__=="__main__":
    main()
