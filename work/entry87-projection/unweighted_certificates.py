"""Certify exhaustion of all alternative doubled sets and verify each geometric cut."""
import argparse,gzip,json,re
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from punctured_lift import project
from punctured_pit import examine,groups
from solve import BANK,BANK_HASH,save


def run(file,checker):
    data=BANK.read_bytes();assert sha256(data).hexdigest()==BANK_HASH
    bank=json.loads(data);g=groups();receipts=[]
    archive=Path(file.stem+"-certificates.zip")
    with ZipFile(archive,"w",ZIP_STORED) as z:
        for entry in json.loads(file.read_text()):
            i=entry["index"];W,sources=g[i];sets=set()
            for s,a in sources:
                P,sw=project(bank[s]["vertex_sequence"],a);sets.add(tuple(sorted(P[j] for j in sw)))
            assert len(sets)==entry["known"]
            for x in entry["other"]:sets.add(tuple(sorted(x["doubled"])))
            assert len(sets)==entry["known"]+len(entry["other"])
            if entry["status"]=="forced":
                C={v for v in W if sum((v^(1<<j)) in W for j in range(8))<=2}
                assert sets=={tuple(sorted(C))} and len(C)+len(W)==192
                continue
            with TemporaryDirectory() as folder:
                r=examine(W,str(i),250000,checker,192,sorted(sets),folder)
                assert r["status"]=="UNSAT"
                for cycle in r["dynamic"]:
                    S=set(cycle)
                    assert len(S)==len(cycle)<192
                    assert all(sum((v^(1<<j)) in S for j in range(9))==2 for v in S)
                for kind in ("cnf","core"):
                    p=Path(folder)/f"punctured-pit-proof-{i}.{kind}.gz"
                    assert sha256(gzip.decompress(p.read_bytes())).hexdigest()==r[kind+"_sha256"]
                    z.write(p,p.name)
                steps=int(re.search(r"using (\d+) resolution steps"," ".join(r["checker"])).group(1))
                receipts.append(dict(index=i,excluded=sorted(sets),cycles=r["dynamic"],cnf_sha256=r["cnf_sha256"],
                                     core_sha256=r["core_sha256"],steps=steps))
    save(Path(file.stem+"-receipts.json"),dict(sha256=sha256(archive.read_bytes()).hexdigest(),certificates=receipts))
    print(file,len(receipts),sum(r["steps"] for r in receipts),archive.stat().st_size,flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("file",type=Path);p.add_argument("checker",type=Path);a=p.parse_args()
    run(a.file,a.checker.resolve())
