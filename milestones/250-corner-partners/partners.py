"""Find or exclude unrestricted opposite-face partners of the seven new corner shapes."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
LAST=HERE.parent/"249-long-parent-joins"
sys.path.insert(0,str(LAST))
import joins
from joins import CHECKER, COMPILER, partner, opposite, archive, save_json
from direct98 import witness
from audit import path_ok, leaves, check_cycle

GEOMETRY=LAST/"geometry.json"
AUDIT=LAST/"audit.json"


def cases():
    inventory=json.loads(joins.INVENTORY.read_bytes())
    old={r["donor_index"]:r["path"] for r in inventory["rows"]}
    bounds={(r["donor"],r["endpoint"]):r["upper"] for r in json.loads(AUDIT.read_bytes())["cases"]}
    out={}
    for row in json.loads(GEOMETRY.read_bytes())["corner_closure"]["new_shapes"]:
        seq=row["path"]; previous=old[row["parent"]]; k=row["position"]
        if (row["id"]!=f"{row['parent']}:{k}" or seq[:k]!=previous[:k] or seq[k+1:]!=previous[k+1:]
                or seq[k]!=row["inserted"] or previous[k]!=row["removed"]
                or sha256(bytes(seq)).hexdigest()!=row["vertex_bytes_sha256"]):
            raise ValueError("Incorrect corner or archived path")
        path_ok(seq,8)
        path_ok(previous,8)
        for end in (0,1):
            order=seq if end==0 else seq[::-1]
            parent=[v^order[0] for v in order]
            out[row["id"],end]=dict(parent=parent,root=order[0],hit=previous[k]^order[0],
                                     old_cap=bounds[row["parent"],end], edges=len(seq)-1)
    return out


def formula(case,n,prefix):
    cnf,chosen=joins.encode(case["parent"],n,prefix,[])
    if n>case["old_cap"]:
        cnf.clauses.append([chosen[case["hit"]]])
        # A prefix of old_cap+1 edges already has to visit the freed site.
        if n>case["old_cap"]+1:
            ns=[chosen[v] for v in partner.NEIGHBOURS[case["hit"]] if v in chosen]
            partner.bounds(cnf,ns,2,len(ns),[])
    return cnf,chosen


def query(case,n,prefix,temp,exe,seconds):
    cnf,chosen=formula(case,n,prefix)
    parent=case["parent"]
    infile,raw=temp/"input.cnf",temp/"trace.lrat"
    until=monotonic()+seconds
    steps=[]
    while True:
        digest=cnf.save(infile)
        raw.unlink(missing_ok=True)
        step=dict(cnf=digest,clauses=len(cnf.clauses),variables=cnf.count)
        steps.append(step)
        try:
            ans=subprocess.run([str(partner.SOLVER),"-q","--seed=1","--lrat","--no-binary",str(infile),str(raw)],
                               capture_output=True,timeout=max(.01,until-monotonic()))
        except subprocess.TimeoutExpired:
            step["outcome"]="open"
            return dict(status="open",steps=steps)
        if ans.returncode==20 and b"s UNSATISFIABLE" in ans.stdout:
            path=HERE/"proofs"/(digest+".lrat.gz")
            path.parent.mkdir(exist_ok=True)
            raw_hash=archive(raw,path)
            replay=subprocess.run([str(exe),str(infile),str(path)],capture_output=True,timeout=90)
            if replay.returncode or not replay.stdout.startswith(b"VERIFIED UNSAT "):
                raise ValueError(("Proof rejected",replay.stderr[-600:]))
            step["outcome"]="excluded"
            return dict(status="excluded",steps=steps,proof=path.relative_to(HERE).as_posix(),raw=raw_hash,
                        compressed=partner.digest(path),replay=replay.stdout.decode().strip())
        if ans.returncode!=10 or b"s SATISFIABLE" not in ans.stdout:
            raise RuntimeError(ans.stderr[-400:])
        truth={int(v) for line in ans.stdout.splitlines() if line.startswith(b"v ")
               for v in line.split()[1:] if int(v)>0}
        selected={v for v,lit in chosen.items() if lit in truth}
        if set(parent)&selected!={0}:
            raise ValueError("Model intersects the full projected parent")
        # The extractor accepts a 96-edge parent. All vertices of a longer
        # parent were forbidden when building the formula and checked just above.
        found,cycles=opposite.extract(parent[:97],n,prefix,selected)
        if found:
            w=witness(parent,found["partner"])
            if n>case["old_cap"] and case["hit"] not in w["partner"][:case["old_cap"]+2]:
                raise ValueError("Incompatible with inherited upper bound")
            step["outcome"]="witness"
            return dict(status="witness",steps=steps,**w)
        step.update(outcome="cycles",cycles=cycles)
        cnf.clauses.extend(check_cycle(c,chosen) for c in cycles)


def pins():
    files=[Path(__file__), GEOMETRY,AUDIT,joins.INVENTORY,Path(joins.__file__),Path(opposite.__file__),
           Path(partner.__file__),joins.LAST/"endpoint94.py",joins.LAST/"certify.py",LAST/"direct98.py",
           LAST/"audit.py",partner.PREV/"free_outer.py",partner.SOURCE/"arc_sat.py",CHECKER,COMPILER,partner.SOLVER]
    return {p.name:partner.digest(p) for p in files}


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--target",type=int,default=192)
    cli.add_argument("--depth",type=int,default=0)
    cli.add_argument("--seconds",type=float,default=6)
    cli.add_argument("--total",type=float,default=145)
    cli.add_argument("--ids",nargs="+")
    args=cli.parse_args()
    table=cases(); file=HERE/f"target-{args.target}.json"
    if not 180<=args.target<=192 or args.depth<0 or min(args.seconds,args.total)<=0:
        cli.error("Invalid search settings")
    data=json.loads(file.read_bytes()) if file.exists() else dict(target=args.target,pins=pins(),records=[])
    if data["pins"]!=pins():raise ValueError("Search dependencies have changed")
    with TemporaryDirectory(prefix="snake250-") as folder:
        temp=Path(folder); exe=temp/"VerifyLrat.exe"
        subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(CHECKER)],check=True,capture_output=True,timeout=60)
        until=monotonic()+args.total
        for (label,end),case in table.items():
            if args.ids and label not in args.ids:continue
            n=args.target-1-case["edges"]
            rows=[r for r in data["records"] if r["id"]==label and r["end"]==end]
            if any(r["status"]=="witness" for r in rows):continue
            tried={tuple(r["prefix"]) for r in rows}
            closed={tuple(r["prefix"]) for r in rows if r["status"]=="excluded"}
            for p in leaves(case["parent"],n,closed,tried):
                if len(p)-1>args.depth:continue
                if monotonic()>=until:return
                item=query(case,n,list(p),temp,exe,min(args.seconds,until-monotonic()))
                data["records"].append(dict(id=label,end=end,length=n,hit=case["hit"],old_cap=case["old_cap"],prefix=list(p),**item))
                save_json(file,data)
                print(label,end,n,p,item["status"],flush=True)
                if item["status"]=="witness":break


if __name__=="__main__":
    main()
