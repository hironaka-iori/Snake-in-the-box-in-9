"""Check the coverage and archived resolution proofs of the entire 97-vertex menu."""
import argparse,gzip,json,re,subprocess
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile
from regrown_middles import middle_menu
from solve import save,defects

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--checker",type=Path)
    p.add_argument("--strong96",action="store_true");a=p.parse_args()
    if a.strong96:
        from promising_96 import ranked
        paths=[(r["index"],r["parent"]) for r in ranked()]
    else:paths=list(enumerate(middle_menu()))
    rows=[]
    with TemporaryDirectory() as folder:
        for i,path in paths:
            prefix="strong96-certified-" if a.strong96 else "middle-certified-"
            receipt=Path(f"{prefix}{i}.json");r=json.loads(receipt.read_bytes());archive=receipt.with_suffix(".zip")
            assert r["index"]==i and r["status"]=="UNSAT" and r["exact_parent"]==path and not defects(path)
            assert len(path)==(96 if a.strong96 else 97) and r["outside_count"]==96 and not r["dynamic"]
            assert sha256(archive.read_bytes()).hexdigest()==r["archive_sha256"]
            steps=int(re.search(r"using (\d+) resolution steps"," ".join(r["checker"])).group(1))
            assert "s VERIFIED" in r["checker"]
            with ZipFile(archive) as z:
                files=[]
                for kind in ("cnf","core"):
                    raw=gzip.decompress(z.read(f"bank-two-proof-middle{i}.{kind}.gz"))
                    assert sha256(raw).hexdigest()==r[kind+"_sha256"]
                    if a.checker:
                        f=Path(folder)/kind;f.write_bytes(raw);files.append(str(f))
                if a.checker:
                    replay=subprocess.run([str(a.checker.resolve()),*files],check=True,capture_output=True)
                    assert b"s VERIFIED" in replay.stdout.splitlines()
            rows.append(dict(index=i,steps=steps,archive=archive.name,archive_sha256=r["archive_sha256"]))
    total=sum(r["steps"] for r in rows)
    if a.strong96:
        assert len(rows)==47
        save(Path("strong96-census.json"),dict(new=47,target_vertices=192,steps=total,cases=rows))
    else:save(Path("regrown-middles-census.json"),dict(known=5,new=46,all_menu_shapes=51,steps=total,cases=rows))
    print(len(rows),sum(r["steps"] for r in rows),flush=True)
