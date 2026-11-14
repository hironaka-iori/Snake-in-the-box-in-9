"""Rebuild each unweighted-projection CNF and replay its archived proof core."""
import argparse,gzip,json,subprocess
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from punctured_pit import groups,examine


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--pack",action="store_true");p.add_argument("--checker",type=Path);a=p.parse_args()
    archive=Path("unweighted-proof-cores.zip")
    if a.pack:
        with ZipFile(archive,"w",ZIP_STORED) as out:
            for f in sorted(Path().glob("unweighted-fibres-*-certificates.zip")):
                with ZipFile(f) as z:
                    for name in z.namelist():
                        if name.endswith(".core.gz"):out.writestr(name,z.read(name))
    g=groups();count=0
    with ZipFile(archive) as z, TemporaryDirectory() as tmp:
        for f in sorted(Path().glob("unweighted-fibres-*-receipts.json")):
            for r in json.loads(f.read_bytes())["certificates"]:
                i=r["index"];W,_=g[i];cnf=Path(tmp)/"input.cnf";core=Path(tmp)/"proof"
                examine(W,str(i),0,desired=192,forbidden_doubles=r["excluded"],rebuild_cnf=cnf,recorded_cycles=r["cycles"])
                assert sha256(cnf.read_bytes()).hexdigest()==r["cnf_sha256"]
                drat=gzip.decompress(z.read(f"punctured-pit-proof-{i}.core.gz"))
                assert sha256(drat).hexdigest()==r["core_sha256"]
                if a.checker:
                    core.write_bytes(drat);result=subprocess.run([str(a.checker.resolve()),str(cnf),str(core)],capture_output=True,check=True)
                    assert b"s VERIFIED" in result.stdout.splitlines()
                count+=1
        assert count==len(z.namelist())==568
    print("Verified",count,flush=True)
