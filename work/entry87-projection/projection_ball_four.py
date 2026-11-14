"""Audit every fourth-shell support decision against the literal source geometries."""
import json
from math import comb
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
from crossing_pair_filter import pair_rows
from punctured_lift import project
from solve import BANK,BANK_HASH,sha256,defects,save

if __name__=="__main__":
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw)
    previous=json.loads(Path("projection-ball-three.json").read_bytes())
    assert previous["sources"]==25 and len(previous["decisions"])==200
    files=set();results=[]
    def read(name):
        f=Path(name);files.add(f);return json.loads(f.read_bytes())
    for i in range(25):
        P,sw=project(bank[i]["vertex_sequence"],5);W=set(P);assert len(sw)==1 and len(W)==191
        for d in (2,3,4):
            a=4-d;k=2+d-a;budget=300000 if k==2 else 150000
            suffix=f"-remove{d}-cross{k}.json";prefix=f"single-hinge-exchange-{i}-"
            report=read(prefix+str(budget)+suffix)
            assert (report["source"],report["removals"],report["crossings"])==(i,d,k)
            controls=[r["witness"] for r in report["control"] if r["witness"]]
            assert len(controls)==1 and len(controls[0])==192 and len({v&255 for v in controls[0]})==192-k and not defects(controls[0])
            roots={v for v in range(256) if sum((v^(1<<j)) in W for j in range(8))<=2+d}
            rows={z["root"]:z for z in report["results"]};assert set(rows)==roots
            remain={r for r,z in rows.items() if z["status"]=="OPEN"}
            assert all(z["status"] in ("OPEN","EXHAUSTED") for z in rows.values())
            extra=[]
            if remain and k==2:
                follow=read(f"two-crossing-pairs-{i}-250000.json")
                pairs={tuple(r["roots"]) for r in pair_rows(W) if r["roots"][0] in remain}
                assert set(follow["open_first_roots"])==remain and {tuple(p) for p in follow["pairs"]}==pairs
                extra=follow["results"];assert {(r["root"],r["second"]) for r in extra}==pairs
            elif remain:
                follow=read(prefix+"1500000"+suffix);extra=follow["results"]
                assert {r["root"] for r in extra}==remain
            assert all(r["status"]=="EXHAUSTED" for r in extra)
            completed=[z for z in rows.values() if z["status"]=="EXHAUSTED"]+extra
            results.append(dict(source=i,removed=d,added=a,crossings=k,first_roots=len(roots),refined=sorted(remain),
                                refinements=len(extra),complete_decisions=len(completed),cuts=sum(z["cycle_cuts"] for z in completed),
                                indexed_choices=comb(191,d)*comb(65,a)))
    archive=Path("projection-ball-four-inputs.zip")
    with ZipFile(archive,"w",ZIP_DEFLATED,compresslevel=6) as z:
        for f in sorted(files):z.write(f,f.name)
    total=sum(r["indexed_choices"] for r in results);previous_total=previous["indexed_support_changes_with_positive_crossing"]
    out=dict(shell_choices=total,through_four=total+previous_total,cases=results,
             completed_decisions=sum(r["complete_decisions"] for r in results),cycle_cuts=sum(r["cuts"] for r in results),
             input_count=len(files),archive_sha256=sha256(archive.read_bytes()).hexdigest())
    save(Path("projection-ball-four.json"),out);print(total,out["through_four"],out["completed_decisions"],out["cycle_cuts"],len(files))
