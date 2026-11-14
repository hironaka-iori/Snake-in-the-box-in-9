"""Independently replay a deep-search UNSAT result. Keep a receipt and packed proof."""
import argparse
import gzip
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import shutil
import subprocess
from exact_cover import components_partition
from saturation import separation
from solve import model,paths,save


def digest(file):
    h=sha256()
    with file.open("rb") as f:
        for b in iter(lambda:f.read(1<<20), b""): h.update(b)
    return h.hexdigest()


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("case",type=Path)
    parser.add_argument("--checker",type=Path,required=True)
    parser.add_argument("--replay-only",action="store_true")
    args=parser.parse_args()
    row=json.loads(args.case.read_text())
    assert row["status"]=="UNSAT"
    bits=row["bits"]; q=paths()[1]
    families=row["cliques"]
    tr=components_partition(q,bits)
    for fam in families:
        assert len({a%2 for a in fam})==1 and len(set(fam))==len(fam)
        assert all(separation(tr[a],tr[b])<=1 for a,b in combinations(fam,2))
    prefix=Path("certificate-"+"".join(map(str,bits)))
    cnf=prefix.with_suffix(".cnf");proof=prefix.with_suffix(".drat")
    old=prefix.with_suffix(".json")
    if args.replay_only:
        receipt=json.loads(old.read_text())
        for f,s in [(cnf,"cnf"),(proof,"drat")]:
            if not f.exists() or digest(f)!=receipt[s+"_sha256"]:
                archive=Path(str(f)+".gz")
                parts=sorted(f.parent.glob(archive.name+".part*"))
                if archive.exists():
                    archives=[archive]
                elif parts:
                    # Parts are independent, ordered gzip members.
                    archives=parts
                else:
                    raise FileNotFoundError(archive)
                with f.open("wb") as dst:
                    for a in archives:
                        with gzip.open(a,"rb") as src:shutil.copyfileobj(src,dst)
            assert digest(f)==receipt[s+"_sha256"]
    else:
        result=model(q,bits,anchor_families=families,certificate=prefix)
        assert result["status"]=="UNSAT"
        receipt=dict(bits=bits,cliques=families,result=result,cnf_sha256=digest(cnf),drat_sha256=digest(proof))
    p=subprocess.run([str(args.checker.resolve()),str(cnf),str(proof)],capture_output=True)
    log=p.stdout.decode(errors="replace")
    assert p.returncode==0 and "s VERIFIED" in log.splitlines(),log[-800:]
    if not args.replay_only:
        receipt["checker_tail"]=log.splitlines()[-8:]
        for f in (cnf,proof):
            with f.open("rb") as src,Path(str(f)+".gz").open("wb") as dst:
                with gzip.GzipFile(fileobj=dst,mode="wb",filename="",mtime=0,compresslevel=5) as gz:
                    shutil.copyfileobj(src,gz)
        save(old,receipt)
    print("VERIFIED",bits,flush=True)
