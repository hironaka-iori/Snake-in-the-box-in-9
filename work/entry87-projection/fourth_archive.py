"""Replay every final-layer DRAT proof after packing its formula and extracted core."""
import argparse,gzip,json,re,subprocess
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from solve import save


def run(checker):
    file=Path("unrestricted-fourth-0-210-180000-checked.json");rows=json.loads(file.read_text())["results"]
    assert len(rows)==210 and all(r["status"]=="UNSAT" for r in rows)
    un=Path("unrestricted-fourth-certificates.zip")
    with ZipFile(un,"w",compression=ZIP_STORED) as z:
        for i,r in enumerate(rows):
            assert r["index"]==i
            for ext in ("cnf","core"):
                f=Path(f"free-last-proof-all-{i}.{ext}.gz");z.write(f,f.name)
    total=0
    with ZipFile(un) as z,TemporaryDirectory() as tmp:
        for i,r in enumerate(rows):
            command=[str(checker)]
            for ext in ("cnf","core"):
                raw=gzip.decompress(z.read(f"free-last-proof-all-{i}.{ext}.gz"))
                assert sha256(raw).hexdigest()==r[ext+"_sha256"]
                dest=Path(tmp)/ext;dest.write_bytes(raw);command.append(str(dest))
            run=subprocess.run(command,capture_output=True,check=True)
            assert b"s VERIFIED" in run.stdout.splitlines()
            total+=int(re.search(rb"using (\d+) resolution steps",run.stdout).group(1))
            dom=set(r["domain"])
            for cycle in r["cuts"]:
                covered=set(cycle)
                assert covered<=dom and all(sum((x^(1<<b)) in covered for b in range(7))==2 for x in covered)
    report=dict(total=len(rows),occurrences=sum(r["occurrences"] for r in rows),inferences=total,
                cycles=sum(len(r["cuts"]) for r in rows),archive_sha256=sha256(un.read_bytes()).hexdigest())
    save(Path("unrestricted-fourth-proof-index.json"),report);print(report,flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("checker",type=Path);a=p.parse_args();run(a.checker.resolve())
