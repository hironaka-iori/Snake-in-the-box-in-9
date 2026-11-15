"""Archive independently replayed proofs for the parity-preserving middle replacements."""
import argparse,gzip,json,os,re
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from free_last_drat import decide
from replace_middle import menu
from solve import save

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int);args=p.parse_args()
    home=Path.cwd();checker=(home/"drat-check.exe").resolve()
    cases=menu();assert json.loads(json.dumps(cases))==json.loads(Path("replaced-middle-menu.json").read_bytes())
    rows=[];archive=home/f"replacement-proofs-{args.start}-{args.stop}.zip"
    with ZipFile(archive,"w",ZIP_STORED) as z:
        for i in range(args.start,min(args.stop,len(cases))):
            r=cases[i];a,b=r["first"],r["last"];W=(set(range(256))-(set(a)|set(b)))|{a[0],b[0]}
            with TemporaryDirectory(dir=home) as tmp:
                try:
                    os.chdir(tmp);tag=f"replacement-{i}"
                    proof=decide(W,r["target"],350000,tag,checker,b[0],8)
                    assert proof["status"]=="UNSAT" and not proof["cuts"] and "s VERIFIED" in proof["checker"]
                    for k in ("cnf","core"):
                        name=f"free-last-proof-{tag}.{k}.gz"
                        assert sha256(gzip.decompress(Path(name).read_bytes())).hexdigest()==proof[k+"_sha256"]
                        z.write(name,name)
                finally:os.chdir(home)
            steps=int(re.search(r"using (\d+) resolution steps"," ".join(proof["checker"])).group(1))
            rows.append(dict(index=i,steps=steps,cnf_sha256=proof["cnf_sha256"],core_sha256=proof["core_sha256"]))
    save(home/f"replacement-proofs-{args.start}-{args.stop}.json",dict(cases=rows,sha256=sha256(archive.read_bytes()).hexdigest()))
    print(len(rows),sum(r["steps"] for r in rows),archive.stat().st_size,flush=True)
