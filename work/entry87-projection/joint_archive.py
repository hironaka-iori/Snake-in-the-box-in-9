"""Compact, replayable archive of the complete 25 by 6 paired-face refutations."""
import argparse
from hashlib import sha256
import gzip,json,re,shutil,subprocess
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from solve import save


def paths(i,n):
    return (Path(f"joint-faces-pair{i}-5-{n}-totalizer-checked.json"),
            Path(f"joint-cert-pair{i}-5-{n}.cnf.gz"),Path(f"joint-cert-pair{i}-5-{n}.core.gz"))


def pack():
    rows=[]
    for n in range(94,100):
        file=Path(f"joint-certificates-{n}.zip")
        with ZipFile(file,"w",compression=ZIP_STORED) as archive:
            for i in range(25):
                receipt,cnf,core=paths(i,n)
                r=json.loads(receipt.read_text())
                assert r["status"]=="UNSAT" and r["sizes"]==[n,193-n] and r["seed"]==i
                assert r["freedom"]==5 and r["dynamic_cycles"]==[] and "s VERIFIED" in r["checker"]
                for f in (cnf,core):
                    assert sha256(gzip.decompress(f.read_bytes())).hexdigest()==r[f.suffixes[0][1:]+"_sha256"]
                for f in (receipt,cnf,core):archive.write(f,f.name)
                steps=int(re.search(r"using (\d+) resolution steps"," ".join(r["checker"])).group(1))
                rows.append(dict(seed=i,first=n,second=193-n,source=r["source"],inferences=steps,
                                 conflicts=r["stats"]["conflicts"],cnf_sha256=r["cnf_sha256"],
                                 core_sha256=r["core_sha256"]))
    save(Path("joint-certified-census.json"),dict(cases=rows,
         archives={f.name:sha256(f.read_bytes()).hexdigest() for f in sorted(Path(".").glob("joint-certificates-*.zip"))}))
    print(len(rows),sum(r["inferences"] for r in rows),flush=True)


def replay(checker):
    manifest=json.loads(Path("joint-certified-census.json").read_text())
    assert {(r["seed"],r["first"]) for r in manifest["cases"]}==set((i,n) for i in range(25) for n in range(94,100))
    done=0
    with TemporaryDirectory() as folder:
        cnf=Path(folder)/"case.cnf";core=Path(folder)/"proof.drat"
        for name,digest in manifest["archives"].items():
            archive=Path(name);assert sha256(archive.read_bytes()).hexdigest()==digest
            n=int(archive.stem.split("-")[-1])
            with ZipFile(archive) as z:
                for i in range(25):
                    record,formula,proof=paths(i,n)
                    r=json.loads(z.read(record.name))
                    for source,dest,key in ((formula,cnf,"cnf"),(proof,core,"core")):
                        raw=gzip.decompress(z.read(source.name))
                        assert sha256(raw).hexdigest()==r[key+"_sha256"];dest.write_bytes(raw)
                    proc=subprocess.run([str(checker),str(cnf),str(core)],capture_output=True)
                    assert proc.returncode==0 and b"s VERIFIED" in proc.stdout.splitlines()
                    done+=1
    print("Replayed",done,"irredundant proof files.",flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--replay",type=Path);a=p.parse_args()
    if a.replay:replay(a.replay.resolve())
    else:pack()
