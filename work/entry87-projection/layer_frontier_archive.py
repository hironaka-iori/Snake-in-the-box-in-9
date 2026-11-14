"""Reassemble the final 41 decisions and replay every proof from a portable archive."""
import gzip,json,re,subprocess
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from solve import defects,save

rows=sorted((r for f in Path().glob("resolved-layer-*-150000-1.json") for r in json.loads(f.read_text())),key=lambda r:r["index"])
inputs=json.loads(Path("one-layer-frontier.json").read_text())["cases"]
assert len(rows)==len(inputs)==41 and all(r["status"]=="EXHAUSTED" for r in rows)
proofs={};success=0;parity_only=0
for i,(r,case) in enumerate(zip(rows,inputs)):
    assert i==r["index"]
    ruled=set();last_cap=case["last_upper"];A=case["first"];C=case["third"]
    for split in r["splits"]:
        b,d=split["middle_size"],split["last_size"];assert b+d==case["required_sum"]
        for which,size in (("last",d),("middle",b)):
            if which not in split:continue
            s=split[which];label="final" if which=="last" else "middle"
            if s["status"]=="FOUND":
                q=s["path"];assert len(q)==size and not defects(q)
                assert q[0]==(C[-1] if which=="last" else A[-1])
                if which=="middle":assert q[-1]==C[0]
                assert set(q)<=set(case[label+"_domain"]);success+=1
            else:
                assert s["status"]=="UNSAT" and not s["cuts"]
                proofs[f"free-last-proof-frontier-{i}-{label}-{size}"]=s
                if which=="last":last_cap=min(last_cap,size-1)
                else:ruled.add(size)
    required={b for b in range(case["required_sum"]-last_cap,case["middle_upper"]+1)
              if (b-1)%2==(A[-1]^C[0]).bit_count()%2}
    assert required<=ruled
    parity_only+=int(not r["splits"])
archive=Path("one-layer-frontier-certificates.zip")
with ZipFile(archive,"w",compression=ZIP_STORED) as z:
    for prefix in sorted(proofs):
        for kind in ("cnf","core"):
            name=f"{prefix}.{kind}.gz";z.write(name,name)
steps=0
with ZipFile(archive) as z,TemporaryDirectory() as tmp:
    for prefix,s in sorted(proofs.items()):
        cmd=[str(Path("drat-check.exe").resolve())]
        for kind in ("cnf","core"):
            raw=gzip.decompress(z.read(f"{prefix}.{kind}.gz"));assert sha256(raw).hexdigest()==s[kind+"_sha256"]
            tmpfile=Path(tmp)/kind;tmpfile.write_bytes(raw);cmd.append(str(tmpfile))
        out=subprocess.run(cmd,capture_output=True,check=True).stdout
        assert b"s VERIFIED" in out.splitlines()
        steps+=int(re.search(rb"using (\d+) resolution steps",out).group(1))
report=dict(cases=len(rows),parity_only=parity_only,proofs=len(proofs),steps=steps,
            single_arm_witnesses=success,archive_sha256=sha256(archive.read_bytes()).hexdigest())
save(Path("one-layer-frontier-verification.json"),report);print(report)
