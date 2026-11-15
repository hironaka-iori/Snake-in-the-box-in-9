"""Index and replay the integer bounds and checked refutations for dense seven-face shapes."""
import argparse
import gzip
import json
from hashlib import sha256
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from forest_orbit_weights import bound
from dense_eight import components
from solve import save


def audit(verify_weights,checker):
    classes=json.loads(Path("seven-deletion-classes.json").read_bytes())
    result={}
    for pop in (64,63,62):
        records=[]
        for i,item in enumerate(classes[str(pop)]):
            fixed=set(item["forest"])
            weights=Path(f"forest-role-weight-{pop}-{i}.json")
            listed=json.loads(weights.read_bytes())
            assert set(listed["fixed"])==fixed and listed["size"]==117
            common=dict(index=i,labelled=item["labelled"])
            if listed["max_edges"]<104:
                if verify_weights:assert bound(fixed,117,listed["certificate"])==listed
                records.append(dict(**common,status="EXCLUDED",method="integer weights",
                                    bound=listed["max_edges"],receipt=weights.name))
                continue
            candidates=[]
            for file in Path(".").glob(f"dense8-class-{pop}-{i}-*-checked.json"):
                r=json.loads(file.read_bytes())
                if r["status"]!="UNSAT":continue
                assert set(r["fixed"])==fixed and r["size"]==117 and r["component_limit"]==13
                assert "s VERIFIED" in r["checker"]
                for cycle in r["cycles"]:
                    literal=set(cycle)
                    assert literal&set(range(128))<=fixed
                    parts=components(literal,8)
                    assert len(parts)==1 and parts[0][0]==len(literal)
                prefix=file.with_suffix("").name+"-proof"
                size=Path(prefix+".core.gz").stat().st_size
                candidates.append((size,file, prefix,r))
            if not candidates:
                records.append(dict(**common,status="OPEN"));continue
            _,receipt,prefix,r=min(candidates)
            files=[]
            with TemporaryDirectory() as tmp:
                for kind in ("cnf","core"):
                    f=Path(prefix+"."+kind+".gz");raw=gzip.decompress(f.read_bytes())
                    assert sha256(raw).hexdigest()==r[kind+"_sha256"]
                    if checker:
                        target=Path(tmp)/kind;target.write_bytes(raw);files.append(str(target))
                if checker:
                    checked=run([str(checker),*files],capture_output=True,check=True)
                    assert b"s VERIFIED" in checked.stdout.splitlines()
            records.append(dict(**common,status="EXCLUDED",method="resolution",receipt=receipt.name,
                                formula=prefix+".cnf.gz",proof=prefix+".core.gz"))
        result[pop]=dict(classes=len(records),excluded=sum(r["status"]=="EXCLUDED" for r in records),
                         labelled=sum(r["labelled"] for r in records if r["status"]=="EXCLUDED"),records=records)
    return result


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--verify-weights",action="store_true")
    p.add_argument("--checker",type=Path);a=p.parse_args()
    result=audit(a.verify_weights,a.checker.resolve() if a.checker else None)
    save(Path("dense-facet-audit.json"),result)
    print({n:(r["excluded"],r["classes"],r["labelled"]) for n,r in result.items()})
