"""Solve each whole middle case and preserve its independently replayed CNF and proof."""
import argparse,json,os
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from bank_two_arms import examine
from regrown_middles import middle_menu
from solve import save

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=3000000);p.add_argument("--checker",type=Path,default=Path("drat-check.exe"))
    p.add_argument("--strong96",action="store_true");a=p.parse_args()
    home=Path.cwd();checker=a.checker.resolve()
    if a.strong96:
        from promising_96 import ranked
        cases=[(r["index"],r["parent"]) for r in ranked()]
    else:cases=list(enumerate(middle_menu()))
    for i,parent in cases[a.start:a.stop]:
        name=f"strong96-certified-{i}" if a.strong96 else f"middle-certified-{i}"
        report=home/(name+".json");archive=home/(name+".zip")
        if report.exists():
            saved=json.loads(report.read_bytes())
            if saved["status"]=="UNSAT" and sha256(archive.read_bytes()).hexdigest()==saved["archive_sha256"]:continue
        with TemporaryDirectory(dir=home) as temp:
            try:
                os.chdir(temp);tag=f"middle{i}";r=examine(dict(parent=parent),tag,a.budget,checker,192 if a.strong96 else 193)
                if r["status"]=="UNSAT":
                    with ZipFile(archive,"w",ZIP_STORED) as z:
                        for kind in ("cnf","core"):
                            name=f"bank-two-proof-{tag}.{kind}.gz";z.write(name,name)
                    r["archive_sha256"]=sha256(archive.read_bytes()).hexdigest()
                save(report,dict(index=i,**r))
            finally:os.chdir(home)
        if r["status"]=="FOUND":break
