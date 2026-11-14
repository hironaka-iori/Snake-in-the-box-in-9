"""Regenerate or replay the certificate for fixed coordinates {0,2,4}."""
import argparse
import gzip
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import shutil
import subprocess
from solve import paths,model
from exact_cover import components_partition
from saturation import separation


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--checker",type=Path,required=True)
    ap.add_argument("--use-archive",action="store_true")
    args=ap.parse_args()
    root=Path(__file__).resolve().parent
    summary=json.loads((root/"certificate-135678.json").read_text())
    q=paths()[1]
    bits=summary["bits"]
    anchors=summary["anchors"]
    trace=components_partition(q,bits)
    assert len(set(anchors))==32 and {a%2 for a in anchors}=={1}
    assert all(separation(trace[a],trace[b])<=1 for a,b in combinations(anchors,2))
    p=root/"certificate-135678"
    cnf=p.with_suffix(".cnf")
    proof=p.with_suffix(".drat")
    if args.use_archive:
        for filename in (cnf,proof):
            archive=filename.with_suffix(filename.suffix+".gz")
            with gzip.open(archive,"rb") as src,filename.open("wb") as dst:
                shutil.copyfileobj(src,dst)
    else:
        r=model(q,bits,anchors=anchors,certificate=p)
        assert r["status"]=="UNSAT"
    for file,key in [(cnf,"cnf_sha256"),(proof,"drat_sha256")]:
        with file.open("rb") as f:
            h=sha256()
            for b in iter(lambda:f.read(1024*1024),b""):
                h.update(b)
        assert h.hexdigest()==summary[key]
    check=subprocess.run([str(args.checker.resolve()),str(cnf),str(proof)],capture_output=True)
    text=check.stdout.decode(errors="replace")
    if check.returncode or "s VERIFIED" not in text.splitlines():
        raise RuntimeError(text[-1000:])
    print("Verified both artifact hashes, 32 anchors, and the complete DRAT refutation.")


if __name__=="__main__":
    main()
