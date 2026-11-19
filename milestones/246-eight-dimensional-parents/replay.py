"""Regenerate and check every saved CNF and its independently replayed LRAT refutation."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import subprocess

from ceiling import encode, template
from free_outer import HERE, NEIGHBOURS
from placements import verify


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def cycle_cut(cycle, chosen, fixed):
    points=set(cycle)
    if len(points)<4 or len(points)!=len(cycle) or not points<=fixed|set(chosen):
        raise ValueError("Invalid cycle cut vertices")
    start=min(points)
    stack=[start]
    seen={start}
    for v in stack:
        neighbours=points.intersection(NEIGHBOURS[v])
        if len(neighbours)!=2:
            raise ValueError("Cut does not describe an induced cycle")
        for w in neighbours-seen:
            stack.append(w)
            seen.add(w)
    if seen!=points:
        raise ValueError("Cycle disconnected")
    return [-chosen[v] for v in cycle if v in chosen]


def main():
    source=HERE/"ceiling.json"
    record=json.loads(source.read_bytes())
    rows=record["records"]
    middles=record["middles"]
    expected={(o[0],a,b) for o in record["crossing_orbits"] for a in range(93,99)
              for b in range(93,99) if a+b>=191}
    if {(r["q"],r["a"],r["b"]) for r in rows}!=expected or len(rows)!=len(expected):
        raise ValueError("Incomplete ceiling enumeration")
    control=record["positive_control"]["path"]
    if len(control)!=192:
        raise ValueError("Incorrect 191-edge lower witness")
    control_pairs=verify(control,9)
    compiler=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    checker=HERE/"VerifyLrat.cs"
    previous_q=None
    checks=[]
    with TemporaryDirectory(prefix="q9-lrat-replay-") as tmp:
        folder=Path(tmp)
        exe=folder/"VerifyLrat.exe"
        cmd=[str(compiler),"/nologo","/optimize+","/out:"+str(exe),str(checker)]
        subprocess.run(cmd,check=True,capture_output=True)
        executable_hash=digest(exe)
        cnf_file=folder/"case.cnf"
        for r in rows:
            if r["status"]!="native_exclusion":
                continue
            q,a,b=r["q"],r["a"],r["b"]
            if q!=previous_q:
                base=template(middles,q)
                previous_q=q
            cnf,chosen,fixed=encode(middles,q,a,b,base)
            final=r["attempts"][-1]
            for run in r["attempts"][:-1]:
                for cycle in run.get("cycles",[]):
                    cnf.clauses.append(cycle_cut(cycle,chosen,fixed))
            if cnf.save(cnf_file)!=final["cnf_sha256"]:
                raise ValueError(("CNF digest",q,a,b))
            proof=HERE/final["lrat"]
            digest_lrat=sha256()
            with gzip.open(proof,"rb") as f:
                for block in iter(lambda:f.read(65536),b""):
                    digest_lrat.update(block)
            if digest_lrat.hexdigest()!=final["lrat_sha256"]:
                raise ValueError(("LRAT digest",q,a,b))
            out=subprocess.run([str(exe),str(cnf_file),str(proof)],capture_output=True,timeout=30)
            if out.returncode:
                raise ValueError((q,a,b,out.stdout[-250:],out.stderr[-450:]))
            checks.append(dict(q=q,a=a,b=b,cnf_sha256=final["cnf_sha256"],lrat_sha256=final["lrat_sha256"],
                               result=out.stdout.decode("ascii").strip()))
    output=dict(enumeration_sha256=digest(source),compiler_sha256=digest(compiler),checker_source_sha256=digest(checker),
                checker_executable_sha256=executable_hash,verified=len(checks),covered=Counter(r["status"] for r in rows),
                control_pairs=control_pairs,cases=checks)
    (HERE/"proof-replay.json").write_text(json.dumps(output,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("LRAT refutations checked",len(checks),"191-edge witness pairs",control_pairs)


if __name__=="__main__":
    main()
