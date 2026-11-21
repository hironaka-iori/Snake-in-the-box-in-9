"""Certify rooted partner bounds shared by several 96-edge arms."""
from argparse import ArgumentParser
from hashlib import sha256
import gzip
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE=Path(__file__).resolve().parent
PRIOR=HERE.parent/"252-shorter-reference-segments"
sys.path.insert(0,str(PRIOR))
import partners
from partners import previous as solver, canonical_root
from partners251 import file_hash, read, path_ok, require
from collections import Counter

TARGET=95
LEDGER=HERE/"group-caps.json"


def inventory():
    closure=read(HERE/"closure.json")
    weights=read(HERE/"thresholds.json")
    old=set(read(PRIOR/"census-68.json")["all_ids"])
    chosen={weights["identities"][int(i)] for i in weights["donor20"]["97"]["above_floor"]}
    require(closure["closed"] and len(chosen)==71 and len(chosen-old)==18,"Terminal family mismatch")
    roots={}
    for label,p in closure["paths"].items():
        if label in old: continue
        require(len(p)==97,"Unexpected new length")
        for end,order in enumerate((p,p[::-1])):
            key,root,axes=canonical_root(order)
            roots[key]=dict(shape=label,end=end,path=root,axes=axes,priority=label in chosen)
    require(len(roots)==348,"New root census differs")
    files=[Path(__file__),HERE/"closure.json",HERE/"thresholds.json",PRIOR/"census-68.json",
           PRIOR/"partners.py",Path(solver.__file__),Path(solver.joins.partner.__file__),
           solver.joins.CHECKER,solver.joins.COMPILER,solver.joins.partner.SOLVER,PRIOR/"TrimLrat.cs"]
    return roots,{p.name:file_hash(p) for p in files}


def groups(keys,blocked,floor):
    waiting=set(keys)
    while waiting:
        first=min(waiting)
        group=[first]
        common=blocked[first]
        waiting.remove(first)
        while waiting:
            key=max(sorted(waiting),key=lambda k:len(common & blocked[k]))
            shared=common & blocked[key]
            if len(shared)<floor: break
            common=shared
            group.append(key)
            waiting.remove(key)
        yield group,common


def trace_selected(selected):
    adjacent={v:set(solver.joins.partner.NEIGHBOURS[v]) & selected for v in selected}
    ends=[v for v,ns in adjacent.items() if len(ns)==1]
    require(len(selected)==96 and 0 in ends and len(ends)==2 and all(1<=len(ns)<=2 for ns in adjacent.values()),
            "Wrong induced degrees")
    p=[0]
    while True:
        children=adjacent[p[-1]]-set(p)
        if not children:break
        require(len(children)==1,"Endpoint component branches")
        p.append(children.pop())
    if len(p)==96:
        path_ok(p,8)
        return p,[]
    left=selected-set(p)
    cycles=[]
    while left:
        group={left.pop()}
        queue=list(group)
        for v in queue:
            new=left & adjacent[v]
            queue.extend(sorted(new));group.update(new);left-=new
        cycles.append(sorted(group))
    return None,cycles


def formula(blocked,cycles):
    cnf,chosen=solver.model([0]+sorted(blocked),TARGET,[])
    for cycle in cycles:cnf.clauses.append(solver.check_cycle(cycle,chosen))
    return cnf,chosen


def search(blocked,seconds,work,checker,trimmer):
    cycles=[]
    until=monotonic()+seconds
    while True:
        cnf,chosen=formula(blocked,cycles)
        input_file=work/"instance.cnf";raw=work/"trace.lrat"
        key=cnf.save(input_file)
        base=dict(blocked=sorted(blocked),target=TARGET,cycles=cycles,variables=cnf.count,clauses=len(cnf.clauses))
        try:
            run=subprocess.run([str(solver.joins.partner.SOLVER),"-q","--seed=1","--lrat","--no-binary",
                                str(input_file),str(raw)],capture_output=True,timeout=max(.01,until-monotonic()))
        except subprocess.TimeoutExpired:
            return key,dict(**base,status="open")
        if run.returncode==20 and b"s UNSATISFIABLE" in run.stdout:
            full=work/"untrimmed.gz"
            solver.joins.archive(raw,full)
            raw.unlink()
            tiny=work/"cut.lrat";spool=work/"hints.bin"
            subprocess.run([str(trimmer),str(len(cnf.clauses)),str(full),str(spool),str(tiny)],
                           check=True,capture_output=True,timeout=100)
            spool.unlink()
            archive=HERE/"proofs"/(key+".lrat.gz")
            archive.parent.mkdir(exist_ok=True)
            raw_digest=solver.joins.archive(tiny,archive)
            tiny.unlink()
            report=solver.check_proof(input_file,archive,checker)
            return key,dict(**base,status="excluded",proof=archive.relative_to(HERE).as_posix(),
                            raw=raw_digest,compressed=file_hash(archive),replay=report)
        require(run.returncode==10 and b"s SATISFIABLE" in run.stdout,"Unexpected SAT exit")
        truth={int(x) for line in run.stdout.splitlines() if line.startswith(b"v ") for x in line.split()[1:]}
        path,extra=trace_selected({v for v,lit in chosen.items() if lit in truth})
        if path:return key,dict(**base,status="path",partner=path)
        cycles.extend(extra)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--all",action="store_true")
    cli.add_argument("--replay",action="store_true")
    cli.add_argument("--seconds",type=int,default=4)
    cli.add_argument("--total",type=int,default=150)
    cli.add_argument("--floor",type=int,default=85)
    args=cli.parse_args()
    roots,pins=inventory()
    data=read(LEDGER) if LEDGER.exists() else dict(pins=pins,records={})
    require(data["pins"]==pins,"Input changed")
    rows=data["records"];allowed={k:set(v["path"][1:]) for k,v in roots.items()}
    def save():solver.joins.save_json(LEDGER,data)
    def remaining():
        masks=[set(r["blocked"]) for r in rows.values() if r["status"]=="excluded"]
        return [k for k,b in allowed.items() if (args.all or roots[k]["priority"]) and not any(m<=b for m in masks)]
    with TemporaryDirectory(prefix="snake253-obstacle-") as folder:
        tmp=Path(folder);checker=tmp/"VerifyLrat.exe";trimmer=tmp/"TrimLrat.exe"
        for src,exe in ((solver.joins.CHECKER,checker),(PRIOR/"TrimLrat.cs",trimmer)):
            subprocess.run([str(solver.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],check=True)
        if args.replay:
            for key,r in rows.items():
                blocked=set(r["blocked"]);cnf,chosen=formula(blocked,r["cycles"]);input_file=tmp/"verify.cnf"
                require(cnf.save(input_file)==key and cnf.count==r["variables"] and len(cnf.clauses)==r["clauses"],
                        "Formula mismatch")
                if r["status"]=="excluded":
                    path=HERE/r["proof"]
                    require(file_hash(path)==r["compressed"] and file_hash(path,gzip.open)==r["raw"] and
                            solver.check_proof(input_file,path,checker)==r["replay"],"Certificate mismatch")
                elif r["status"]=="path":
                    path_ok(r["partner"],8)
                    require(r["partner"][0]==0 and len(r["partner"])==96 and blocked.isdisjoint(r["partner"]),
                            "Invalid relaxed witness")
        else:
            until=monotonic()+args.total
            def visit(keys,common):
                if monotonic()>=until:return
                prior=next(((k,r) for k,r in rows.items() if r["blocked"]==sorted(common)),None)
                if prior and prior[1]["status"]!="open":
                    key,row=prior
                else:
                    key,row=search(common,args.seconds if len(keys)>1 else 2*args.seconds,tmp,checker,trimmer)
                    rows[key]=row;save()
                    print(len(keys),len(common),row["status"],key[:10],flush=True)
                if len(keys)>1 and row["status"]!="excluded":
                    split=(len(keys)+1)//2
                    for part in (keys[:split],keys[split:]):
                        visit(part,set.intersection(*(allowed[k] for k in part)))
            for group,common in groups(remaining(),allowed,args.floor):
                visit(group,common)
                if monotonic()>=until:break
    coverage={}
    for key,r in roots.items():
        b=allowed[key]
        proof=next((k for k,row in rows.items() if row["status"]=="excluded" and set(row["blocked"])<=b),None)
        if proof:coverage[key]=dict(shape=r["shape"],end=r["end"],proof=proof)
    witnesses=[]
    for row in rows.values():
        if row["status"]!="path":continue
        for key,b in allowed.items():
            if b.isdisjoint(row["partner"]):
                full=roots[key]["path"][::-1]+[v+256 for v in row["partner"]]
                path_ok(full,9);require(len(full)==193,"Invalid 192-edge join")
                witnesses.append(dict(root=key,path=full))
    summary=dict(ledger_sha256=file_hash(LEDGER),checked=args.replay,covered=coverage,
                 all_new_roots=len(roots),priority_roots=sum(r["priority"] for r in roots.values()),
                 priority_covered=sum(roots[k]["priority"] for k in coverage),status_counts=Counter(r["status"] for r in rows.values()),
                 witnesses=witnesses)
    solver.joins.save_json(HERE/("group-replay.json" if args.replay else "group-current.json"),summary)
    print("coverage",len(coverage),summary["priority_covered"],dict(summary["status_counts"]),len(witnesses),flush=True)


if __name__=="__main__":main()
