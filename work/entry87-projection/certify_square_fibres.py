"""Independently verify each exact square-fibre formula, then archive formulas and proof cores."""
import argparse,gzip,json,re,subprocess
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from square_fibers import project_square,search
from solve import BANK,BANK_HASH,save


def run(i,checker):
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;q=json.loads(raw)[i]["vertex_sequence"]
    archive=Path(f"square-fibre-certificates-{i:03}.zip");receipt=Path(f"square-fibre-receipt-{i:03}.json")
    if archive.exists() and receipt.exists():
        assert sha256(archive.read_bytes()).hexdigest()==json.loads(receipt.read_text())["archive_sha256"]
        return
    rows=[]
    with ZipFile(archive,"w",compression=ZIP_STORED) as z:
        for axes in combinations(range(9),2):
            key=f"{i}-{axes[0]}-{axes[1]}";trace,old=project_square(q,axes)
            r=search(trace,old,45000,key,checker)
            assert r["status"]=="UNSAT"
            stem="square-fibre-proof-"+key
            for ext in ("cnf","core"):
                file=Path(f"{stem}.{ext}.gz");z.write(file,file.name)
            rows.append(dict(axes=axes,**r))
    with ZipFile(archive) as z,TemporaryDirectory() as tmp:
        for r in rows:
            a,b=r["axes"];stem=f"square-fibre-proof-{i}-{a}-{b}";cmd=[str(checker)]
            for ext in ("cnf","core"):
                raw=gzip.decompress(z.read(f"{stem}.{ext}.gz"))
                assert sha256(raw).hexdigest()==r[ext+"_sha256"]
                dest=Path(tmp)/ext;dest.write_bytes(raw);cmd.append(str(dest))
            out=subprocess.run(cmd,capture_output=True,check=True).stdout
            assert b"s VERIFIED" in out.splitlines()
            r["steps"]=int(re.search(rb"using (\d+) resolution steps",out).group(1))
            for ext in ("cnf","core","drat","cnf.gz","core.gz"):
                Path(f"{stem}.{ext}").unlink()
    save(receipt,dict(source=i,archive_sha256=sha256(archive.read_bytes()).hexdigest(),rows=rows))
    print(i,sum(r["steps"] for r in rows),archive.stat().st_size,flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--checker",type=Path,default=Path("drat-check.exe"));a=p.parse_args()
    if a.stop-a.first>1:
        import sys
        for i in range(a.first,a.stop):
            subprocess.run([sys.executable,__file__,str(i),str(i+1),"--checker",str(a.checker)],check=True)
    else:run(a.first,a.checker.resolve())
