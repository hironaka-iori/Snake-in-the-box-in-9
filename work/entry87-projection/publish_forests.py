"""Build the compact index of all independently replayed fixed-forest certificates."""
import json
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile, ZIP_STORED
from solve import save


def pack():
    groups=[];batch=[];size=0
    cases=[]
    for i in range(111):
        receipt=Path(f"forest-face-{i}-193-checked.json")
        r=json.loads(receipt.read_text());f=Path(f"forest-refutation-{i}-193.zip")
        assert r["status"]=="UNSAT" and not r["dynamic"] and r["index"]==i
        assert r["replayed_steps"]>0 and sha256(f.read_bytes()).hexdigest()==r["archive_sha256"]
        if size+f.stat().st_size>36*(1<<20):
            groups.append(batch);batch=[];size=0
        batch.append((i,receipt,f));size+=f.stat().st_size
        cases.append(dict(index=i,source=r["source"],inferences=r["replayed_steps"],
                          cnf_sha256=r["cnf_sha256"],core_sha256=r["core_sha256"],archive_sha256=r["archive_sha256"]))
    if batch:groups.append(batch)
    files=[]
    for i,batch in enumerate(groups):
        part=Path(f"face-forest-certificates-{i}.zip")
        with ZipFile(part,"w",compression=ZIP_STORED) as z:
            for j,receipt,f in batch:
                z.write(receipt,receipt.name)
                with ZipFile(f) as inside:
                    for record in inside.namelist():z.writestr(record,inside.read(record))
        files.append(dict(name=part.name,sha256=sha256(part.read_bytes()).hexdigest(),indices=[c[0] for c in batch]))
    save(Path("face-forest-certified.json"),dict(proofs=cases,archives=files,total_steps=sum(r["inferences"] for r in cases)))
    print(len(cases),len(files),sum(r["inferences"] for r in cases),flush=True)


def replay(checker):
    import gzip,subprocess
    from tempfile import TemporaryDirectory
    ledger=json.loads(Path("face-forest-certified.json").read_text());seen=set();steps=0
    with TemporaryDirectory() as folder:
        for block in ledger["archives"]:
            file=Path(block["name"]);assert sha256(file.read_bytes()).hexdigest()==block["sha256"]
            with ZipFile(file) as z:
                for i in block["indices"]:
                    assert i not in seen;seen.add(i)
                    r=json.loads(z.read(f"forest-face-{i}-193-checked.json"));command=[str(checker)]
                    for ext in ("cnf","core"):
                        data=gzip.decompress(z.read(f"forest-face-proof-{i}-193.{ext}.gz"))
                        assert sha256(data).hexdigest()==r[ext+"_sha256"]
                        target=Path(folder)/ext;target.write_bytes(data);command.append(str(target))
                    run=subprocess.run(command,capture_output=True,check=True);assert b"s VERIFIED" in run.stdout.splitlines()
                    steps+=r["replayed_steps"]
    assert seen==set(range(111)) and steps==ledger["total_steps"]
    print("Verified 111 archived proofs",steps,flush=True)


if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser();p.add_argument("--replay",type=Path);a=p.parse_args()
    if a.replay:replay(a.replay.resolve())
    else:pack()
