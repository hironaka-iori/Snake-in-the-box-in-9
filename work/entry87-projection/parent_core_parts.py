"""Split or verify independently compressed ordered parts of a large DRAT core."""
import argparse,gzip,json,shutil,subprocess
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory


def split(prefix,receipt):
    total=sha256();parts=[]
    with Path(str(prefix)+".core").open("rb") as src:
        while chunk:=src.read(128<<20):
            part=Path(str(prefix)+f".core.gz.part{len(parts):02d}")
            with part.open("wb") as f:
                with gzip.GzipFile(filename="",fileobj=f,mode="wb",mtime=0,compresslevel=5) as gz:gz.write(chunk)
            total.update(chunk);parts.append(part)
    assert total.hexdigest()==receipt["core_sha256"]
    print(len(parts),sum(f.stat().st_size for f in parts))


def check(prefix,receipt,checker=None):
    parts=sorted(prefix.parent.glob(prefix.name+".core.gz.part*"))
    if not parts:parts=[Path(str(prefix)+".core.gz")]
    total=sha256()
    with TemporaryDirectory() as tmp:
        core=Path(tmp)/"proof.drat";cnf=Path(tmp)/"input.cnf"
        with core.open("wb") as f:
            for part in parts:
                with gzip.open(part,"rb") as source:
                    while data:=source.read(1<<20):total.update(data);f.write(data)
        assert total.hexdigest()==receipt["core_sha256"]
        raw=gzip.decompress(Path(str(prefix)+".cnf.gz").read_bytes())
        assert sha256(raw).hexdigest()==receipt["cnf_sha256"];cnf.write_bytes(raw)
        if checker:
            replay=subprocess.run([str(checker),str(cnf),str(core)],capture_output=True,check=True)
            assert b"s VERIFIED" in replay.stdout.splitlines()
    print("verified",prefix,len(parts))


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("case",type=int);p.add_argument("--split",action="store_true")
    p.add_argument("--checker",type=Path);a=p.parse_args()
    prefix=Path(f"parent-proof-{a.case}--1");r=json.loads(Path(f"parent-sat-{a.case}--1-checked.json").read_text())
    if a.split:split(prefix,r)
    check(prefix,r,a.checker.resolve() if a.checker else None)
