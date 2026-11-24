"""Solve for an unrestricted complementary arm; retain checkable contradictions and ordered paths."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS/"262-common-forbidden-sites"))
import masks
geometry = masks.p.joins.partner


def load(path):
    return json.loads(path.read_bytes())


def save(path, obj):
    path.write_bytes((json.dumps(obj,separators=(",",":"))+"\n").encode())


def model(blocked, n, prefix, cycles, seen):
    assert 0 not in blocked and prefix[0] == 0 and not blocked.intersection(prefix)
    geometry.verify(prefix, 8)
    cnf = geometry.Formula()
    choose = {v:cnf.variable() for v in range(256) if v not in blocked}
    ends = {v:cnf.variable() for v in choose if v and v.bit_count()%2 == n%2}
    cnf.exactly(list(ends.values()),1)
    for parity, count in ((0,n//2+1),(1,(n+1)//2)):
        cnf.exactly([lit for v,lit in choose.items() if v.bit_count()%2==parity],count)
    cnf.clauses.append([choose[0]])
    for v,lit in choose.items():
        near = [choose[u] for u in geometry.NEIGHBOURS[v] if u in choose]
        if v==0:
            geometry.bounds(cnf,near,1,1,[])
        elif v in ends:
            end = ends[v]
            cnf.clauses.append([-end,lit])
            geometry.bounds(cnf,near,1,2,[-lit])
            geometry.bounds(cnf,near,0,1,[-end])
            geometry.bounds(cnf,near,2,len(near),[-lit,end])
        else:
            geometry.bounds(cnf,near,2,2,[-lit])
    for i,v in enumerate(prefix):
        cnf.clauses.append([choose[v]])
        if i+1<len(prefix):
            incident = set(prefix[max(0,i-1):i]+prefix[i+1:i+2])
            cnf.clauses.extend([-choose[u]] for u in geometry.NEIGHBOURS[v] if u in choose and u not in incident)
    geometry.face_bounds(cnf,choose)
    cnf.clauses.extend(geometry.cycle_clause(choose,c) for c in cycles)
    for path in seen:
        assert len(path)==n+1 and path[0]==0 and not set(path)&blocked
        geometry.verify(path,8)
        cnf.clauses.append([-choose[v] for v in sorted(path)])
    return cnf,choose


def solve(folder,tmp,tools,blocked,n,prefix,cycles,seen,seconds):
    stop = monotonic()+seconds
    formula, trace = tmp/"partner.cnf",tmp/"proof.lrat"
    masks.fixed.HERE = folder
    cycles=list(cycles)
    while True:
        cnf, chosen = model(blocked,n,prefix,cycles,seen)
        h = cnf.save(formula)
        result = dict(cnf=h,clauses=len(cnf.clauses),prefix=prefix,cycles=cycles)
        try:
            trace.unlink(missing_ok=True)
            call=subprocess.run([str(geometry.SOLVER),"-q","--seed=1","--lrat","--no-binary",str(formula),str(trace)],
                                capture_output=True,timeout=max(.01,stop-monotonic()))
        except subprocess.TimeoutExpired:
            return dict(status="open",**result)
        if call.returncode==20 and b"s UNSATISFIABLE" in call.stdout:
            proof=folder/"proofs"/(h+".lrat.gz")
            proof.parent.mkdir(exist_ok=True)
            result.update(status="excluded",proof=proof.relative_to(folder).as_posix(),
                          raw=masks.p.joins.archive(trace,proof),compressed=masks.digest(proof))
            result["replay"]=masks.p.check_proof(formula,proof,tools[0])
            masks.fixed.compact(tmp,*tools,result)
            return result
        if call.returncode!=10 or b"s SATISFIABLE" not in call.stdout:
            raise ValueError((call.returncode,call.stderr[-300:]))
        truth={int(x) for line in call.stdout.splitlines() if line.startswith(b"v ") for x in line.split()[1:]}
        sites={v for v,k in chosen.items() if k in truth}
        assert len(sites)==n+1 and 0 in sites
        path=[0]
        remaining=sites-{0}
        while True:
            options=remaining.intersection(geometry.NEIGHBOURS[path[-1]])
            if not options:
                break
            u,=options
            path.append(u)
            remaining.remove(u)
        assert path[:len(prefix)]==prefix
        if not remaining:
            geometry.verify(path,8)
            return dict(status="witness",path=path,**result)
        while remaining:
            group=[min(remaining)]
            remaining.remove(group[0])
            for v in group:
                extra=remaining.intersection(geometry.NEIGHBOURS[v])
                remaining-=extra
                group.extend(sorted(extra))
            geometry.cycle_clause(chosen,group)
            cycles.append(sorted(group))


def branches(parent,depth):
    front=[[0]]
    for _ in range(depth):
        front=[p+[u] for p in front for u in geometry.next_vertices(parent,p)]
    return front


def query_root(dest,case,n,rows,tools,tmp,seconds,depth,census):
    parent=case["parent"]
    known={tuple(x) for x in case["partners"].values() if len(x)==n+1} if census else set()
    if len(known)!=len(set(tuple(sorted(x)) for x in known)):
        raise ValueError("Duplicate rooted orders")
    seen=list(map(list,sorted(known)))
    for prefix in branches(parent,depth):
        tag=",".join(map(str,prefix))
        if any(rows.get(",".join(map(str,prefix[:j])),{}).get("status")=="excluded" for j in range(1,len(prefix)+1)):
            continue
        prev=rows.get(tag,{})
        if prev.get("status")=="witness":
            continue
        answer=solve(dest,tmp,tools,set(parent[1:]),n,prefix,prev.get("cycles",[]),seen,seconds)
        if answer["status"]=="witness":
            joined=parent[::-1]+[v+256 for v in answer["path"]]
            geometry.verify(joined,9)
            answer["joined"]=joined
        rows[tag]=answer
        yield answer


def main():
    ap=ArgumentParser()
    ap.add_argument("--seconds",type=float,default=3)
    ap.add_argument("--depth",type=int,default=0)
    ap.add_argument("--target",type=int,default=192)
    ap.add_argument("--census",action="store_true")
    ap.add_argument("--which",choices=["published","opposite","all"],default="all")
    cli=ap.parse_args()
    src=HERE/"parents.json"
    parents=load(src)["parents"]
    tag=str(cli.target)+("-census" if cli.census else "")
    out=HERE/("partner-"+tag+".json")
    record=load(out) if out.exists() else dict(parents_sha256=masks.digest(src),roots={})
    assert record["parents_sha256"]==masks.digest(src)
    with TemporaryDirectory() as work:
        tmp=Path(work)
        tools=masks.compilers(tmp)
        for key,case in sorted(parents.items(),key=lambda kv:(not bool(kv[1]["partners"]),kv[0])):
            if not case["from_191"] or (cli.which!="all" and (cli.which=="published")!=bool(case["partners"])):
                continue
            n=cli.target-len(case["parent"])
            rows=record["roots"].setdefault(key,{})
            for ans in query_root(HERE,case,n,rows,tools,tmp,cli.seconds,cli.depth,cli.census):
                save(out,record)
                print(key[:9],n,ans["prefix"],ans["status"],flush=True)
                if ans["status"]=="witness" and cli.target>=192:
                    return

if __name__=="__main__":
    main()
