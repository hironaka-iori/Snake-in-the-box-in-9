"""Check first-use parent nogoods and the independently reconstructed distance model."""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import subprocess
from parent_firstuse import search
from parent_family import construct
from rerun_deep_certificate import digest
from solve import save


def verify(case,budget,checker):
    row=search(case,budget,True)
    assert row["status"]=="UNSAT"
    data,_=construct(case)
    canonical=set(map(tuple,row["normalized_nogoods"]))
    known=set(map(tuple,data["nogoods"]))
    assert canonical<=known
    for assignment in canonical:
        named={}
        for u,v in zip(assignment,assignment[1:]):
            symbol=(u^v).bit_length()-1
            assert symbol==named.setdefault(symbol,len(named))
    prefix=Path(f"parent-firstproof-{case}")
    cnf=prefix.with_suffix(".cnf");proof=prefix.with_suffix(".drat");core=prefix.with_suffix(".core")
    a=subprocess.run([str(checker),str(cnf),str(proof),"-l",str(core)],capture_output=True)
    assert a.returncode==0 and b"s VERIFIED" in a.stdout.splitlines()
    b=subprocess.run([str(checker),str(cnf),str(core)],capture_output=True)
    assert b.returncode==0 and b"s VERIFIED" in b.stdout.splitlines()
    row["check"]=b.stdout.decode(errors="replace").splitlines()[-10:]
    for f in (cnf,core):
        row[f.suffix[1:]+"_sha256"]=digest(f)
        with f.open("rb") as src,Path(str(f)+".gz").open("wb") as dst:
            with gzip.GzipFile(filename="",fileobj=dst,mode="wb",mtime=0,compresslevel=5) as z:
                shutil.copyfileobj(src,z)
    save(prefix.with_suffix(".json"),row)
    print("VERIFIED",case,row["base"])


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("case",type=int);parser.add_argument("--checker",type=Path,required=True)
    parser.add_argument("--budget",type=int,default=600000)
    a=parser.parse_args();verify(a.case,a.budget,a.checker.resolve())
