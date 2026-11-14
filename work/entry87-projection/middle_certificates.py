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
    p.add_argument("--budget",type=int,default=3000000);p.add_argument("--checker",type=Path,default=Path("drat-check.exe"));a=p.parse_args()
    home=Path.cwd();checker=a.checker.resolve();paths=middle_menu()
    for i in range(a.start,min(a.stop,len(paths))):
        report=home/f"middle-certified-{i}.json";archive=home/f"middle-certified-{i}.zip"
        if report.exists():
            saved=json.loads(report.read_bytes())
            if saved["status"]=="UNSAT" and sha256(archive.read_bytes()).hexdigest()==saved["archive_sha256"]:continue
        with TemporaryDirectory(dir=home) as temp:
            try:
                os.chdir(temp);tag=f"middle{i}";r=examine(dict(parent=paths[i]),tag,a.budget,checker)
                if r["status"]=="UNSAT":
                    with ZipFile(archive,"w",ZIP_STORED) as z:
                        for kind in ("cnf","core"):
                            name=f"bank-two-proof-{tag}.{kind}.gz";z.write(name,name)
                    r["archive_sha256"]=sha256(archive.read_bytes()).hexdigest()
                save(report,dict(index=i,**r))
            finally:os.chdir(home)
        if r["status"]=="FOUND":break
