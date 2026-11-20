"""Find the exact partner length at each endpoint of the saved 98-edge snake."""
from argparse import ArgumentParser
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from time import monotonic

import joins
from joins import CHECKER, COMPILER, HERE, INVENTORY, LAST, archive, opposite, partner, save_json


def rooted_data(folder):
    inventory = json.loads(INVENTORY.read_bytes())
    donors_file = partner.PREV/"donors.json"
    if partner.digest(donors_file)!=inventory["source_sha256"]:
        raise ValueError("Changed donor array")
    bank = json.loads(donors_file.read_bytes())["shapes"]
    source = next(r for r in inventory["rows"] if r["edges"]==98)
    path = source["path"]
    partner.verify(path,8)
    if len(path)!=99 or source["donor_index"]!=20 or bank[20]["path"]!=path or [path[0],path[-1]]!=[0,78]:
        raise ValueError("Changed 98-edge parent")
    inherited = json.loads((HERE/"partners-92.json").read_bytes())["records"]
    parents, transfers = {}, {}
    for root,donor,end in ((0,15,0),(78,17,1)):
        oriented = path if root==0 else path[::-1]
        full = [v^root for v in oriented]
        small = partner.rooted_parent(bank[donor]["path"],end)
        if full[:97]!=small:
            raise ValueError("The frozen 96-edge subarm differs")
        cert = next(r for r in inherited if r["donor"]==donor and r["endpoint"]==end
                    and r["prefix"]==[0] and r["status"]=="excluded")
        cnf,_ = opposite.encode(small,92,[0],cert["cycles"])
        if (cnf.save(folder/"subarm.cnf")!=cert["cnf_sha256"] or
                partner.digest(HERE/cert["proof"])!=cert["gzip_sha256"] or
                not cert["checker"].startswith("VERIFIED UNSAT ")):
            raise ValueError("The published subarm certificate differs")
        parents[root] = full
        transfers[str(root)] = dict(length_excluded=92,donor=donor,endpoint=end,
                                    deleted_free_end_vertices=full[97:],cnf_sha256=cert["cnf_sha256"],
                                    proof=cert["proof"],gzip_sha256=cert["gzip_sha256"],
                                    checker=cert["checker"])
    return parents,transfers


def witness(parent,path):
    length = len(path)-1
    if (not path or path[0]!=0 or set(path)&set(parent)!={0} or
            sum(v.bit_count()%2==0 for v in path)!=length//2+1):
        raise ValueError("Wrong partner root, intersection or parity")
    joined = parent[::-1]+[256+v for v in path]
    for seq,dim in ((parent,8),(path,8),(joined,9)):
        partner.verify(seq,dim)
    return dict(partner_edges=length,joined_edges=len(joined)-1,partner=path,joined=joined,
                all_pairs={k:len(seq)*(len(seq)-1)//2 for k,seq in
                           (("parent",parent),("partner",path),("joined",joined))})


def solve(parent,n,prefix,temp,checker,seconds,seed,accept):
    cnf,chosen = opposite.encode(parent,n,prefix)
    formula,raw = temp/"root.cnf",temp/"root.lrat"
    cycles,attempts = [],[]
    until = monotonic()+seconds
    while monotonic()<until:
        key = cnf.save(formula)
        raw.unlink(missing_ok=True)
        attempt = dict(cnf_sha256=key)
        attempts.append(attempt)
        try:
            result = subprocess.run([str(partner.SOLVER),"-q","--seed="+str(seed),"--lrat","--no-binary",
                                     str(formula),str(raw)],capture_output=True,
                                    timeout=max(.01,until-monotonic()))
        except subprocess.TimeoutExpired:
            attempt["outcome"]="timeout"
            break
        if result.returncode==20 and b"s UNSATISFIABLE" in result.stdout:
            rebuilt,_ = opposite.encode(parent,n,prefix,cycles)
            if rebuilt.save(formula)!=key:
                raise ValueError("Regenerated full-parent formula differs")
            path=HERE/"direct98-proofs"/(key+".lrat.gz")
            path.parent.mkdir(exist_ok=True)
            raw_hash=archive(raw,path)
            report=subprocess.run([str(checker),str(formula),str(path)],capture_output=True,timeout=90)
            if report.returncode or not report.stdout.startswith(b"VERIFIED UNSAT "):
                raise ValueError(("Rejected proof",report.stdout[-300:],report.stderr[-300:]))
            attempt["outcome"]="verified_unsat"
            return dict(status="excluded",attempts=attempts,cycles=cycles,cnf_sha256=key,
                        proof=path.relative_to(HERE).as_posix(),raw_sha256=raw_hash,
                        gzip_sha256=partner.digest(path),checker=report.stdout.decode().strip())
        if result.returncode!=10 or b"s SATISFIABLE" not in result.stdout:
            raise RuntimeError(("Unexpected solver output",result.stderr[-300:]))
        truth={int(t) for l in result.stdout.splitlines() if l.startswith(b"v ") for t in l.split()[1:] if int(t)>0}
        selected={v for v,k in chosen.items() if k in truth}
        if set(parent)&selected!={0}:
            raise ValueError("A selected vertex collides with the full parent")
        # The inherited extractor checks every selected vertex and finds all cycles;
        # its length-specific witness builder takes a 96-edge subarm. The full
        # ordered join is verified independently against all 99 parent vertices below.
        found,extra=opposite.extract(parent[:97],n,prefix,selected)
        if found:
            accept(found["partner"])
            attempt["outcome"]="connected"
            return dict(status="witness",attempts=attempts,cycles=cycles,**witness(parent,found["partner"]))
        component=selected-set().union(*map(set,extra))
        route=[0]
        remaining=component-{0}
        while remaining:
            ns=remaining.intersection(partner.NEIGHBOURS[route[-1]])
            if len(ns)!=1:
                raise ValueError("The root component is not a path")
            v=ns.pop()
            route.append(v)
            remaining.remove(v)
        accept(route)
        attempt.update(outcome="disconnected",cycles=extra,root_component_edges=len(route)-1)
        cnf.clauses.extend(partner.cycle_clause(chosen,c) for c in extra)
        cycles.extend(extra)
    return dict(status="open",attempts=attempts,cycles=cycles)


def leaves(parent,n,rows):
    known={tuple(r["prefix"]):r["status"] for r in rows}
    def visit(p):
        if known.get(p)=="excluded":
            return []
        if p not in known or len(p)-1>=n:
            return [p]
        # Scan the whole cube to cross-check each geometric branch.
        candidates=[v for v in range(256) if v not in parent and v not in p and
                    (v^p[-1]).bit_count()==1 and all((v^w).bit_count()!=1 for w in p[:-1])]
        if sorted(partner.next_vertices(parent,p))!=candidates:
            raise ValueError("Incomplete continuation list")
        return [q for v in candidates for q in visit(p+(v,))]
    return sorted(visit((0,)),key=lambda p:(len(p),p))


def summary(parent,root,data):
    low=data["witnesses"][str(root)]["partner_edges"]
    high=91
    while high>low:
        rows=[r for r in data["records"] if r["root"]==root and r["length"]==high]
        pending=leaves(parent,high,rows)
        if pending:
            break
        high-=1
    if low>high:
        raise ValueError("Witness exceeds an upper bound")
    return dict(lower=low,upper=high,exact=low==high,open_prefixes=[] if low==high else pending)


def carry_witnesses(data,parents,transfers):
    """Trim a verified 96-parent partner just before its first new obstruction."""
    source_rows=[]
    for path in sorted(HERE.glob("partners-*.json")):
        for row in json.loads(path.read_bytes())["records"]:
            if row["status"]=="witness":
                source_rows.append((path,row["donor"],row["endpoint"],row["partner"]))
    positive=HERE/"witnesses.json"
    if positive.exists():
        for row in json.loads(positive.read_bytes())["records"]:
            if "best" in row:
                source_rows.append((positive,*row["case"],row["best"]["partner"]))
    for root,p in parents.items():
        donor,end=(transfers[str(root)][k] for k in ("donor","endpoint"))
        for source,i,e,route in source_rows:
            if (i,e)!=(donor,end):
                continue
            stop=next((j for j,v in enumerate(route) if j and v in p),len(route))
            if stop-1>data["witnesses"][str(root)]["partner_edges"]:
                data["witnesses"][str(root)]=witness(p,route[:stop])
                data.setdefault("lower_transfers",[]).append(dict(root=root,source=source.name,donor=i,
                         endpoint=e,original_edges=len(route)-1,retained_edges=stop-1))


def main():
    args=ArgumentParser(description=__doc__)
    args.add_argument("--roots",type=int,nargs="+",choices=(0,78),default=[78,0])
    args.add_argument("--floor",type=int,default=88,choices=range(1,92))
    args.add_argument("--depth",type=int,default=2)
    args.add_argument("--seconds",type=float,default=9)
    args.add_argument("--total",type=float,default=110)
    opts=args.parse_args()
    if not 0<=opts.depth<opts.floor or min(opts.seconds,opts.total)<=0:
        args.error("Invalid prefix depth or budget")
    dest=HERE/"direct98.json"
    sources=[Path(__file__),INVENTORY,partner.PREV/"donors.json",Path(joins.__file__),Path(opposite.__file__),
             LAST/"certify.py",Path(partner.__file__),partner.PREV/"free_outer.py",partner.SOURCE/"arc_sat.py",
             CHECKER,COMPILER,partner.SOLVER]
    pins={p.name:partner.digest(p) for p in sources}
    with TemporaryDirectory(prefix="snake249-direct98-") as folder:
        temp=Path(folder)
        parents,transfers=rooted_data(temp)
        data=json.loads(dest.read_bytes()) if dest.exists() else dict(pins=pins,inherited=transfers,
                    roots={str(k):p for k,p in parents.items()},records=[],witnesses={
                        str(k):witness(p,[0]) for k,p in parents.items()})
        if data["pins"]!=pins or data["inherited"]!=transfers or data["roots"]!={str(k):p for k,p in parents.items()}:
            raise ValueError("Checkpoint source differs")
        for root,p in parents.items():
            item=data["witnesses"][str(root)]
            if item!=witness(p,item["partner"]):
                raise ValueError("Checkpoint witness differs")
        carry_witnesses(data,parents,transfers)
        for row in data["records"]:
            if row["status"]=="excluded":
                rebuilt,_=opposite.encode(parents[row["root"]],row["length"],row["prefix"],row["cycles"])
                if (rebuilt.save(temp/"check.cnf")!=row["cnf_sha256"] or
                        partner.digest(HERE/row["proof"])!=row["gzip_sha256"] or
                        not row["checker"].startswith("VERIFIED UNSAT ")):
                    raise ValueError("Changed previous exclusion")
        exe=temp/"VerifyLrat.exe"
        subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(CHECKER)],
                       capture_output=True,check=True,timeout=60)
        data["checker_executable_sha256"]=partner.digest(exe)
        until=monotonic()+opts.total
        data["summary"]={str(r):summary(p,r,data) for r,p in parents.items()}
        save_json(dest,data)
        while monotonic()<until:
            progress=False
            for root in dict.fromkeys(opts.roots):
                p=parents[root]
                mark=data["summary"][str(root)]
                n=mark["upper"]
                queue=[q for q in mark["open_prefixes"] if len(q)-1<=opts.depth]
                if mark["exact"] or n<opts.floor or not queue or monotonic()>=until:
                    continue
                prefix=queue[0]
                def accept(path):
                    record=witness(p,path)
                    if record["partner_edges"]>data["witnesses"][str(root)]["partner_edges"]:
                        data["witnesses"][str(root)]=record
                        data["summary"][str(root)]=summary(p,root,data)
                        save_json(dest,data)
                result=solve(p,n,prefix,temp,exe,min(opts.seconds,until-monotonic()),1,accept)
                data["records"].append(dict(root=root,length=n,prefix=list(prefix),**result))
                data["summary"][str(root)]=summary(p,root,data)
                save_json(dest,data)
                progress=True
                print("root",root,"length",n,"prefix",list(prefix),result["status"],
                      "bounds",data["summary"][str(root)]["lower"],data["summary"][str(root)]["upper"],flush=True)
            if not progress:
                break


if __name__=="__main__":
    main()
