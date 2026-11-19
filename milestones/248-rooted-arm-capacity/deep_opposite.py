"""Continue only class 5, endpoint 1, with an independently reconstructed prefix cover."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess

from opposite import decide, witness
from survey import HERE, PREVIOUS, partner, save_json


def children(parent,prefix):
    # Independent adjacency and chord test, including the root and all earlier sites.
    banned=set(parent)|set(prefix)
    direct=[v for v in range(256) if v not in banned and (v^prefix[-1]).bit_count()==1
            and all((v^u).bit_count()!=1 for u in prefix[:-1])]
    if sorted(partner.next_vertices(parent,prefix))!=direct:
        raise ValueError("First-principles continuation set differs")
    return [tuple(prefix)+(v,) for v in direct]


def cover(parent,n,verified,splits):
    """Return full coverage and the unclosed leaves, without trusting stored counts."""
    def visit(p):
        if p in verified:
            return []
        if p not in splits or len(p)-1>=n:
            return [p]
        result=[]
        actual=children(parent,p)
        if actual!=splits[p]:
            raise ValueError("Saved cover split differs from cube adjacency")
        for c in actual:
            result.extend(visit(c))
        return result
    return visit((0,))


def proof_ok(record):
    if (not record["checker"].startswith("VERIFIED UNSAT ") or
            partner.digest(HERE/record["proof"])!=record["gzip_sha256"]):
        raise ValueError("Inherited certificate or replay receipt differs")


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--seconds",type=float,default=6,help="Solver budget at each prefix")
    cli.add_argument("--total",type=float,default=140,help="Wall-time budget for this invocation")
    cli.add_argument("--depth",type=int,default=3,help="Maximum prefix length in edges")
    args=cli.parse_args()
    if min(args.seconds,args.total)<=0 or not 2<=args.depth<=10:
        cli.error("Invalid budgets")
    original=HERE/"opposite.json"
    audit_file=HERE/"opposite-audit.json"
    source=next(r for r in json.loads(original.read_bytes())["records"] if r["class_id"]==5)
    audit=json.loads(audit_file.read_bytes())
    prior=next(r for r in audit["classes"] if r["class_id"]==5)
    if audit["input_sha256"]!=partner.digest(original) or prior["upper"]!=source["upper"] or source["endpoint"]!=1:
        raise ValueError("Different original ledger or audited bound")
    parent=partner.rooted_parent(partner.parent_arms()[5],1)
    checker=partner.PREV/"VerifyLrat.cs"
    compiler=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    inputs=[Path(__file__),HERE/"opposite.py",HERE/"certify.py",PREVIOUS/"partner.py",
            original,audit_file,checker,compiler,partner.SOLVER,partner.PREV/"comparison.json"]
    pins={p.name:partner.digest(p) for p in inputs}
    dest=HERE/"deep-opposite.json"
    record=json.loads(dest.read_bytes()) if dest.exists() else dict(
        class_id=5,endpoint=1,rooted_parent=parent,pins=pins,initial_upper=source["upper"],
        upper=source["upper"],lower=source["lower"],lower_witness=source["lower_witness"],
        levels={},runs=0,lower_sources={})
    if record["pins"]!=pins or record["rooted_parent"]!=parent:
        raise ValueError("Changed case or proof checkpoint")
    record["runs"]+=1
    def accept(item):
        path=item["partner"]
        clean=witness(parent,path,len(path)-1)
        if clean["joined"]!=item["joined"] or clean["partner_edges"]!=item["partner_edges"]:
            raise ValueError("Lower witness does not reconstruct")
        if clean["partner_edges"]>record["upper"]:
            raise ValueError("Lower witness exceeds checked upper bound")
        if clean["partner_edges"]>record["lower"]:
            record.update(lower=clean["partner_edges"],lower_witness=clean)
    accept(record["lower_witness"])
    accept(source["lower_witness"])
    for name in ("lower-witnesses.json","lower_witnesses.json"):
        lowfile=HERE/name
        if lowfile.is_file():
            data=json.loads(lowfile.read_bytes())
            for r in data["records"]:
                if r["class_id"]==5 and "lower_witness" in r:
                    accept(r["lower_witness"])
            record["lower_sources"][name]=partner.digest(lowfile)
    # Validate the predecessor's geometric coverage of every inherited descent.
    for n in range(93,source["upper"],-1):
        solved={tuple(a["prefix"]) for a in source["length_queries"][str(n)] if a["status"]=="verified_exclusion"}
        audited={tuple(p) for p in prior["complete_exclusions"][str(n)]}
        if not audited<=solved or cover(parent,n,solved,{(0,):children(parent,(0,))}):
            raise ValueError("Incomplete inherited upper-bound chain")
    for key,level in record["levels"].items():
        for q in level["queries"]:
            if q["status"]=="verified_exclusion":
                proof_ok(q)
        if int(key)>record["upper"] and not level.get("complete"):
            raise ValueError("Missing completed level")
    with TemporaryDirectory(prefix="q8-deep-end5-") as tmp:
        folder=Path(tmp)
        exe=folder/"VerifyLrat.exe"
        subprocess.run([str(compiler),"/nologo","/optimize+","/out:"+str(exe),str(checker)],
                       capture_output=True,check=True,timeout=60)
        record["checker_executable_sha256"]=partner.digest(exe)
        until=monotonic()+args.total
        while record["upper"]>record["lower"] and monotonic()<until:
            n=record["upper"]
            level=record["levels"].setdefault(str(n),dict(queries=[],splits=[],complete=False))
            inherited=[q for q in source["length_queries"].get(str(n),[]) if q["status"]=="verified_exclusion"]
            for q in inherited:
                proof_ok(q)
            level["inherited"]=[dict(prefix=q["prefix"],cnf_sha256=q["cnf_sha256"],proof=q["proof"],
                                     raw_sha256=q["raw_sha256"],gzip_sha256=q["gzip_sha256"]) for q in inherited]
            verified={tuple(q["prefix"]) for q in inherited+level["queries"] if q["status"]=="verified_exclusion"}
            splits={tuple(s["prefix"]):[tuple(c) for c in s["children"]] for s in level["splits"]}
            def split(p):
                if p not in splits:
                    kids=children(parent,p)
                    splits[p]=kids
                    level["splits"].append(dict(prefix=p,children=kids))
            if n==source["upper"]:
                split((0,))
                for p in children(parent,(0,)):
                    if p not in verified:
                        split(p)
            attempted=set()
            while monotonic()<until and record["lower"]<n:
                pending=cover(parent,n,verified,splits)
                level["open_leaves"]=[list(p) for p in sorted(pending,key=lambda p:(len(p),p))]
                if not pending:
                    level["complete"]=True
                    record["upper"]=n-1
                    break
                possible=[p for p in pending if p not in attempted]
                if not possible:
                    break
                # Breadth first: every uncovered second step is queried before
                # entering the descendants of a timed-out second step.
                p=min(possible,key=lambda p:(len(p),p))
                attempted.add(p)
                repeat=sum(tuple(r["prefix"])==p for r in level["queries"])
                tag=f"deep5-e1-n{n}-r{repeat}-"+"-".join(map(str,p))
                budget=min(args.seconds,until-monotonic())
                if budget<=0:
                    break
                trial=decide(parent,n,list(p),folder,exe,budget,tag,seed=1+repeat)
                level["queries"].append(trial)
                if trial["status"]=="witness":
                    accept(trial)
                elif trial["status"]=="verified_exclusion":
                    verified.add(p)
                elif len(p)-1<min(n,args.depth):
                    split(p)
                level["open_leaves"]=[list(c) for c in sorted(cover(parent,n,verified,splits),key=lambda c:(len(c),c))]
                save_json(dest,record)
                print("length",n,"prefix",p,trial["status"],"unclosed leaves",len(level["open_leaves"]),flush=True)
            # Account for an exclusion arriving on the last permitted query.
            pending=cover(parent,n,verified,splits)
            if not pending:
                level["complete"]=True
                record["upper"]=n-1
            if record["lower"]>record["upper"]:
                raise ValueError("Contradictory path and certificate")
            save_json(dest,record)
            if record["upper"]==n:
                break
    # Reconstruct every descent recorded by this new ledger once more.
    for n in range(source["upper"],record["upper"],-1):
        level=record["levels"][str(n)]
        proven={tuple(q["prefix"]) for q in level["inherited"]}
        proven.update(tuple(q["prefix"]) for q in level["queries"] if q["status"]=="verified_exclusion")
        splits={tuple(s["prefix"]):[tuple(c) for c in s["children"]] for s in level["splits"]}
        if not level["complete"] or cover(parent,n,proven,splits):
            raise ValueError("Incomplete independently recovered descent")
    record["status"]="exact" if record["lower"]==record["upper"] else "open"
    save_json(dest,record)
    print("class 5 endpoint 1",record["lower"],record["upper"],record["status"])


if __name__=="__main__":
    main()
