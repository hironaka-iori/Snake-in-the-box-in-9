"""Search four unrestricted outer pieces for two Q7 middles of different lengths."""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import gzip
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PREV=HERE.parent/"246-eight-dimensional-parents"
sys.path.insert(0,str(PREV))
from ceiling import template, inspect, SOLVER
from placements import verify


def unary(cnf,inputs):
    """Output j is true exactly when at least j+1 inputs are true."""
    if len(inputs)<=1:
        return inputs
    half=len(inputs)//2
    left,right=unary(cnf,inputs[:half]),unary(cnf,inputs[half:])
    out=[cnf.variable() for _ in inputs]
    for i in range(len(left)+1):
        for j in range(len(right)+1):
            k=i+j
            if k:
                cnf.clauses.append(([-left[i-1]] if i else [])+([-right[j-1]] if j else [])+[out[k-1]])
            if k<len(out):
                cnf.clauses.append(([left[i]] if i<len(left) else [])+([right[j]] if j<len(right) else [])+[-out[k]])
    return out


def model(middles,q,target):
    cnf,chosen,fixed,ends=template(middles,q)
    lengths=[]
    for x,mid in enumerate(middles):
        legal={a:cnf.variable() for a in range(target-99,99)}
        lengths.append(legal)
        cnf.clauses.append(list(legal.values()))
        cnf.clauses.extend([-u,-v] for u,v in combinations(legal.values(),2))
        for p in range(2):
            def group(v):
                return v>>7==2*x and (v&127).bit_count()%2==p
            counts=unary(cnf,[lit for v,lit in chosen.items() if group(v)])
            forced=sum(group(v) for v in fixed)
            upper=sum((v.bit_count()+1)%2==p for v in mid)
            for a,s in legal.items():
                quota=(a+1)//2+int(a%2==0 and q.bit_count()%2==p)-upper-forced
                if not 0<=quota<=len(counts):
                    cnf.clauses.append([-s])
                else:
                    if quota:
                        cnf.clauses.append([-s,counts[quota-1]])
                    if quota<len(counts):
                        cnf.clauses.append([-s,-counts[quota]])
                if (q.bit_count()+a)%2!=p:
                    cnf.clauses.extend([-s,-e] for v,e in ends.items() if group(v))
    cnf.clauses.extend([-s,-t] for a,s in lengths[0].items() for b,t in lengths[1].items() if a+b+1<target)
    return cnf,chosen,fixed


def partners():
    source=json.loads((HERE/"complementary.json").read_bytes())
    second=sorted(tuple(path) for row in source["records"] if row["length"]==48 for path in row["paths"])
    return source["first"],second


def decide(middles,q,target,folder,tag,budget):
    cnf,chosen,fixed=model(middles,q,target)
    attempts=[]
    remaining=budget
    filename=folder/"case.cnf"
    proof=folder/"proof.lrat"
    while remaining>0:
        row=dict(cnf_sha256=cnf.save(filename))
        attempts.append(row)
        start=monotonic()
        try:
            proc=subprocess.run([str(SOLVER),"--plain","-q","--lrat","--no-binary",str(filename),str(proof)],
                                capture_output=True,timeout=remaining)
        except subprocess.TimeoutExpired:
            row["outcome"]="timeout"
            break
        remaining-=monotonic()-start
        if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
            dest=HERE/"lift-proofs"/(tag+".lrat.gz")
            dest.parent.mkdir(exist_ok=True)
            digest=sha256()
            with proof.open("rb") as inf,dest.open("wb") as of:
                with gzip.GzipFile(filename="",fileobj=of,mode="wb",compresslevel=3,mtime=0) as archive:
                    for chunk in iter(lambda:inf.read(65536),b""):
                        digest.update(chunk)
                        archive.write(chunk)
            row.update(outcome="UNSAT",proof=dest.relative_to(HERE).as_posix(),lrat_sha256=digest.hexdigest())
            return dict(status="excluded",attempts=attempts)
        if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:
            raise RuntimeError((proc.returncode,proc.stderr[:200]))
        positive={int(t) for line in proc.stdout.splitlines() if line.startswith(b"v ") for t in line.split()[1:] if int(t)>0}
        selected=fixed|{v for v,lit in chosen.items() if lit in positive}
        a,b=(sum(v>>8==x for v in selected)-1 for x in range(2))
        if a+b+1<target or max(a,b)>98:
            raise ValueError("Invalid selected arm sizes")
        path,cycles=inspect(selected,middles,q,a,b)
        if path:
            verify(path,9)
            row["outcome"]="connected"
            return dict(status="witness",attempts=attempts,path=path,arm_lengths=[a,b])
        row.update(outcome="disconnected",cycles=cycles)
        cnf.clauses.extend([-chosen[v] for v in cycle if v in chosen] for cycle in cycles)
    return dict(status="unknown",attempts=attempts)


def main():
    first,other=partners()
    target=192
    dest=HERE/"lifts.json"
    pins=dict(input_sha256=sha256((HERE/"complementary.json").read_bytes()).hexdigest(),
              solver_sha256=sha256(SOLVER.read_bytes()).hexdigest(),source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    data=dict(target=target,first=first,rows=[],witness=None,budget=1.0,**pins)
    if dest.is_file():
        data=json.loads(dest.read_bytes())
        if any(data[k]!=v for k,v in pins.items()):
            raise ValueError("Checkpoint inputs differ")
    rows=data["rows"]
    if data["witness"]:
        return
    for i,p in enumerate(other):
        mid=[first,p]
        sites=sorted(set(range(128))-set(first[1:-1])-set(p[1:-1]))
        if len(rows)==i:
            rows.append(dict(index=i,middle=p,sites=sites,results=[]))
        outcome=rows[i]["results"]
        if sites[:len(outcome)]!=[r["q"] for r in outcome]:
            raise ValueError("Checkpoint sites differ")
        with TemporaryDirectory(prefix="q9-247-lift-") as tmp:
            for q in sites[len(outcome):]:
                result=decide(mid,q,target,Path(tmp),f"p{i}-q{q}",1.0)
                outcome.append(dict(q=q,**result))
                if result.get("path"):
                    data["witness"]=result["path"]
                temp=dest.with_suffix(".tmp")
                temp.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
                temp.replace(dest)
                if data["witness"]:
                    break
        print("middle",i,"witness",data["witness"] is not None,"excluded",sum(r["status"]=="excluded" for r in outcome),
              "unresolved",sum(r["status"]=="unknown" for r in outcome),flush=True)
        if data["witness"]:
            break


if __name__=="__main__":
    main()
