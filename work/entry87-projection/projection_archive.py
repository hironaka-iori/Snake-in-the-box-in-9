"""Pack all fixed-shadow formulas and proof cores after independently replaying them."""
import argparse, gzip, json, re, subprocess
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile, ZIP_STORED
from punctured_pit import groups
from solve import save


def pack(checker):
    archive=Path("projected-shadow-cores.zip")
    with ZipFile(archive,"w",compression=ZIP_STORED) as z, TemporaryDirectory() as folder:
        counts=Counter(); steps=0; results=[]; formulas={}
        data=json.loads(Path("punctured-free-order-0-5000.json").read_text())
        group=groups()
        for i,r in enumerate(data):
            P,occ=group[i]; assert r["index"]==i and list(map(tuple,r["sources"]))==occ
            sites=set(P); need=193-len(P)
            capacity=sum(sum((v^(1<<j)) in sites for j in range(8))<=2 for v in sites)
            assert need==r["required"] and capacity==r["possible"]
            counts[r["status"]]+=1
            if r["status"]=="capacity":
                assert capacity<need; continue
            assert r["status"]=="UNSAT" and r["dynamic"]==[]
            base=f"punctured-pit-proof-{i}"; records={}
            for ext in ("cnf","core"):
                f=Path(base+"."+ext+".gz"); raw=gzip.decompress(f.read_bytes())
                records[ext+"_sha256"]=sha256(raw).hexdigest()
                (Path(folder)/ext).write_bytes(raw)
                if ext=="core":z.write(f,f.name)
                else:formulas[i]=f
            cmd=[str(checker),str(Path(folder)/"cnf"),str(Path(folder)/"core")]
            replay=subprocess.run(cmd,capture_output=True,check=True)
            assert b"s VERIFIED" in replay.stdout.splitlines()
            row_steps=int(re.search(rb"using (\d+) resolution steps",replay.stdout).group(1))
            steps+=row_steps
            results.append(dict(index=i,inferences=row_steps,**records))
    assert len(data)==len(group)==1043 and sum(len(r["sources"]) for r in data)==1179
    assert counts=={"capacity":475,"UNSAT":568}
    # Keep each block below 34 MiB for ordinary repository transports.
    blocks=[];batch=[];total=0
    for index,formula in formulas.items():
        if total+formula.stat().st_size>34*(1<<20):
            blocks.append(batch);batch=[];total=0
        batch.append((index,formula));total+=formula.stat().st_size
    if batch:blocks.append(batch)
    indexfiles=[]
    for j,batch in enumerate(blocks):
        f=Path(f"projected-shadow-formulas-{j}.zip")
        with ZipFile(f,"w",compression=ZIP_STORED) as z:
            for i,path in batch:z.write(path,path.name)
        indexfiles.append(dict(file=f.name,sha256=sha256(f.read_bytes()).hexdigest(),indices=[i for i,_ in batch]))
    save(Path("projected-shadow-certified.json"),dict(counts=counts,inferences=steps,proofs=results,
         core_archive_sha256=sha256(archive.read_bytes()).hexdigest(),formula_archives=indexfiles))
    print(dict(counts),steps,len(indexfiles),flush=True)


def replay(checker):
    report=json.loads(Path("projected-shadow-certified.json").read_text())
    proofs={r["index"]:r for r in report["proofs"]}; seen=set()
    archive=Path("projected-shadow-cores.zip")
    assert sha256(archive.read_bytes()).hexdigest()==report["core_archive_sha256"]
    with ZipFile(archive) as cores,TemporaryDirectory() as folder:
        cnf=Path(folder)/"formula"; core=Path(folder)/"core"
        for block in report["formula_archives"]:
            f=Path(block["file"]);assert sha256(f.read_bytes()).hexdigest()==block["sha256"]
            with ZipFile(f) as formulas:
                for i in block["indices"]:
                    assert i not in seen;seen.add(i)
                    base=f"punctured-pit-proof-{i}"
                    for z,key,path in ((formulas,"cnf",cnf),(cores,"core",core)):
                        raw=gzip.decompress(z.read(base+"."+key+".gz"))
                        assert sha256(raw).hexdigest()==proofs[i][key+"_sha256"]
                        path.write_bytes(raw)
                    run=subprocess.run([str(checker),str(cnf),str(core)],capture_output=True,check=True)
                    assert b"s VERIFIED" in run.stdout.splitlines()
    assert seen==set(proofs) and len(seen)==568
    print("Verified",len(seen),"archived shadows",flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("checker",type=Path);p.add_argument("--replay",action="store_true")
    a=p.parse_args();(replay if a.replay else pack)(a.checker.resolve())
