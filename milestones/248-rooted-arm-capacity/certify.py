"""Regenerate and independently replay the sixteen remaining fixed-parent exclusions."""
from pathlib import Path
from tempfile import TemporaryDirectory
from hashlib import sha256
import gzip
import json
import subprocess

from survey import HERE, PREVIOUS, cases, partner, save_json


def archive(raw,path):
    temp = path.with_suffix(".partial")
    digest = sha256()
    with raw.open("rb") as source, temp.open("wb") as target:
        with gzip.GzipFile(filename="",fileobj=target,mode="wb",compresslevel=3,mtime=0) as zipped:
            for block in iter(lambda:source.read(131072),b""):
                digest.update(block)
                zipped.write(block)
    temp.replace(path)
    return digest.hexdigest()


def main():
    source = HERE/"survey.json"
    survey = json.loads(source.read_bytes())
    jobs = cases()
    if ([r["case"] for r in survey["records"]] != [list(c) for c in jobs]
            or any(r["status"]!="native_unsat" for r in survey["records"])):
        raise ValueError("Native exclusions incomplete")
    checker = partner.PREV/"VerifyLrat.cs"
    compiler = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    pins = {p.name:partner.digest(p) for p in (source, HERE/"survey.py",Path(__file__),checker,compiler,partner.SOLVER,
            PREVIOUS/"partner.py", partner.PREV/"free_outer.py", partner.SOURCE/"arc_sat.py",partner.PREV/"comparison.json")}
    proofs = HERE/"proofs"
    proofs.mkdir(exist_ok=True)
    destination = HERE/"certificates.json"
    data = json.loads(destination.read_bytes()) if destination.exists() else dict(pins=pins, records=[])
    if data["pins"] != pins or [r["case"] for r in data["records"]] != [list(c) for c in jobs[:len(data["records"])]]:
        raise ValueError("Changed certificate checkpoint")
    arms = partner.parent_arms()
    with TemporaryDirectory(prefix="snake248-proof-") as tmp:
        temp = Path(tmp)
        exe = temp/"VerifyLrat.exe"
        subprocess.run([str(compiler),"/nologo","/optimize+","/out:"+str(exe),str(checker)],check=True,capture_output=True,timeout=60)
        formula,raw=temp/"case.cnf",temp/"case.lrat"
        for rec in survey["records"][len(data["records"]):]:
            i,e,s = rec["case"]
            parent = partner.rooted_parent(arms[i],e)
            cnf,chosen = partner.encode(parent,[0,s])
            for attempt in rec["attempts"]:
                if cnf.save(formula)!=attempt["cnf"]:
                    raise ValueError("Changed intermediate formula")
                for cycle in attempt["cycles"]:
                    cnf.clauses.append(partner.cycle_clause(chosen,cycle))
            if cnf.save(formula)!=rec["final_cnf"]:
                raise ValueError("Changed final formula")
            path = proofs/f"arm{i}-end{e}-first{s}.lrat.gz"
            for flags in ([],["--plain"]):
                raw.unlink(missing_ok=True)
                try:
                    answer = subprocess.run([str(partner.SOLVER),"-q","--seed=1",*flags,"--lrat","--no-binary",str(formula),str(raw)],
                                            capture_output=True,timeout=40)
                except subprocess.TimeoutExpired:
                    continue
                if answer.returncode!=20 or b"s UNSATISFIABLE" not in answer.stdout:
                    raise ValueError("Unconfirmed solver exclusion")
                digest = archive(raw,path)
                output = subprocess.run([str(exe),str(formula),str(path)],capture_output=True,timeout=90)
                if output.returncode==0 and output.stdout.startswith(b"VERIFIED UNSAT "):
                    break
            else:
                raise RuntimeError(("Certificate pending",i,e,s))
            data["records"].append(dict(case=[i,e,s],solver_flags=flags,cnf_sha256=rec["final_cnf"],proof=path.relative_to(HERE).as_posix(),
                 raw_sha256=digest,gzip_sha256=partner.digest(path),raw_bytes=raw.stat().st_size,verified=output.stdout.decode().strip()))
            save_json(destination,data)
            print("Verified",i,e,s,path.stat().st_size,flush=True)


if __name__=="__main__":
    main()
