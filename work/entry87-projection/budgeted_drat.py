"""Generate and replay the complete target-syndrome certificate files."""
import argparse,gzip,json,subprocess
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED


def files(r):
    return ["dual-union-proof-"+r["tag"]+"."+s+".gz" for s in ("cnf","core")]


def portfolio(receipt,archive,checker=None):
    rows=json.loads(receipt.read_text())
    assert [r["index"] for r in rows]==list(range(131))
    if checker is None:
        with ZipFile(archive,"w",compression=ZIP_STORED) as z:
            for r in rows:
                assert r["status"]=="UNSAT" and r["cycles"]==[]
                for f,s in zip(files(r),("cnf","core")):
                    raw=Path(f).read_bytes();assert sha256(gzip.decompress(raw)).hexdigest()==r[s+"_sha256"]
                    z.writestr(f,raw)
    else:
        with ZipFile(archive) as z,TemporaryDirectory() as folder:
            for r in rows:
                dest=[]
                for f,s in zip(files(r),("cnf","core")):
                    raw=gzip.decompress(z.read(f));assert sha256(raw).hexdigest()==r[s+"_sha256"]
                    p=Path(folder)/("case."+s);p.write_bytes(raw);dest.append(p)
                attempt=subprocess.run([str(checker),*map(str,dest)],check=True,capture_output=True)
                assert b"s VERIFIED" in attempt.stdout.splitlines()
    print(len(rows),sha256(archive.read_bytes()).hexdigest(),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("prefix");p.add_argument("receipt",type=Path)
    p.add_argument("checker",type=Path);a=p.parse_args()
    receipt=json.loads(a.receipt.read_text())
    assert receipt["status"]=="UNSAT"
    with TemporaryDirectory() as folder:
        paths=[]
        for part in ("cnf","core"):
            data=gzip.decompress(Path(a.prefix+"."+part+".gz").read_bytes())
            assert sha256(data).hexdigest()==receipt[part+"_sha256"]
            f=Path(folder)/("proof."+part);f.write_bytes(data);paths.append(f)
        trial=subprocess.run([str(a.checker.resolve()),*map(str,paths)],capture_output=True,check=True)
        assert b"s VERIFIED" in trial.stdout.splitlines()
        print(trial.stdout.decode(errors="replace").splitlines()[-6:],flush=True)
