"""Enumerate extremal partners at the five published joining endpoints."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess
from time import monotonic

from endpoint94 import encode94, extract, joined
from certify import archive
from survey import HERE, partner, save_json
from placements import shape


def main():
    inputs = HERE/"endpoint94.json"
    ten = json.loads(inputs.read_bytes())["records"]
    if len(ten)!=10 or any(r["status"]!="verified_exclusion" for r in ten if r["case"][1]==1):
        raise ValueError("Missing endpoint coverage")
    checker = partner.PREV/"VerifyLrat.cs"
    compiler = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    bank_path = HERE.parents[1]/"work/bank9.json"
    pins = {p.name:partner.digest(p) for p in (inputs,Path(__file__),HERE/"endpoint94.py",bank_path,checker,partner.SOLVER)}
    bank_data = json.loads(bank_path.read_bytes())
    known_words = {shape(r["vertex_sequence"]) for r in bank_data}
    arms = partner.parent_arms()
    dest = HERE/"attainers.json"
    data = json.loads(dest.read_bytes()) if dest.exists() else dict(pins=pins,records=[])
    if data["pins"]!=pins:
        raise ValueError("Inconsistent inputs")
    proofs = HERE/"proofs"
    proofs.mkdir(exist_ok=True)
    with TemporaryDirectory(prefix="snake248-attainers-") as tmp:
        folder=Path(tmp)
        exe=folder/"VerifyLrat.exe"
        subprocess.run([str(compiler),"/nologo","/optimize+","/out:"+str(exe),str(checker)],capture_output=True,check=True)
        formula, raw = folder/"case.cnf",folder/"case.lrat"
        for parent_case in (r for r in ten if r["case"][1]==0):
            i,e=parent_case["case"]
            parent=partner.rooted_parent(arms[i],e)
            if parent!=parent_case["rooted_parent"]:
                raise ValueError("Root label changed")
            row=next((r for r in data["records"] if r["class_id"]==i),None)
            if row is None:
                row=dict(class_id=i,paths=[],cycles=[],status="searching")
                data["records"].append(row)
                for w in parent_case["known_bank_witnesses"]:
                    row["paths"].append(dict(path=w["partner"],seed=w["seed"]))
            if row["status"] in ("exhausted","path_limit","time_limit"):
                continue
            cnf,chosen=encode94(parent)
            seen=set()
            for ent in row["paths"]:
                path=ent["path"]
                w=joined(parent,path)
                member=shape(w["joined"]) in known_words
                if "seed" in ent and not member:
                    raise ValueError("Published positive missing from bank")
                ent["in_bank"]=member
                key=frozenset(path)
                if key in seen:
                    raise ValueError("Duplicate positive set")
                seen.add(key)
            base=cnf.clauses.copy()
            until=monotonic()+65
            while len(seen)<35 and monotonic()<until:
                cnf.clauses=base.copy()
                cnf.clauses.extend([-chosen[v] for v in sorted(w["path"])] for w in row["paths"])
                cnf.clauses.extend(partner.cycle_clause(chosen,c) for c in row["cycles"])
                digest=cnf.save(formula)
                raw.unlink(missing_ok=True)
                try:
                    proc=subprocess.run([str(partner.SOLVER),"-q","--seed=1","--lrat","--no-binary",str(formula),str(raw)],
                                        capture_output=True,timeout=min(35,max(.05,until-monotonic())))
                except subprocess.TimeoutExpired:
                    row["status"]="time_limit"
                    break
                if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
                    proof=proofs/f"attainers-{i}.lrat.gz"
                    rawhash=archive(raw,proof)
                    replay=subprocess.run([str(exe),str(formula),str(proof)],capture_output=True,timeout=90)
                    if replay.returncode!=0 or not replay.stdout.startswith(b"VERIFIED UNSAT "):
                        raise ValueError(("Refutation failed",i,replay.stderr[-200:]))
                    row.update(status="exhausted",cnf_sha256=digest,proof=proof.relative_to(HERE).as_posix(),
                               raw_sha256=rawhash,gzip_sha256=partner.digest(proof),verified=replay.stdout.decode().strip())
                    break
                if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:
                    raise ValueError((i,proc.returncode,proc.stderr[-200:]))
                truth={int(x) for line in proc.stdout.splitlines() if line.startswith(b"v ") for x in line.split()[1:] if int(x)>0}
                w,cycles=extract(parent,[0],{v for v,l in chosen.items() if l in truth})
                if w:
                    path=w["partner"]
                    if frozenset(path) in seen:
                        raise ValueError("Returned blocked witness")
                    seen.add(frozenset(path))
                    row["paths"].append(dict(path=path,in_bank=shape(w["joined"]) in known_words,joined=w["joined"]))
                for cycle in cycles:
                    partner.cycle_clause(chosen,cycle)
                    row["cycles"].append(cycle)
                save_json(dest,data)
            if row["status"]=="searching":
                row["status"]="path_limit" if len(seen)==35 else "time_limit"
            save_json(dest,data)
            print(i,row["status"],"partners",len(row["paths"]),"outside bank",sum(not w["in_bank"] for w in row["paths"]),flush=True)


if __name__=="__main__":
    main()
