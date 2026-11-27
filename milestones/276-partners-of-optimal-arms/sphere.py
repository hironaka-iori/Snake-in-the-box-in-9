"""Classify literal 98-edge Q8 paths at a prescribed site distance from the Carlson path."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess
from inputs276 import HERE,read,save,valid,canonical
from importlib.util import spec_from_file_location, module_from_spec
spec=spec_from_file_location("partner276",HERE/"partners.py")
local=module_from_spec(spec);spec.loader.exec_module(local)
hunt=local.hunt

def encode(g,old,d,cycles,found):
    f=g.Formula()
    x={v:f.variable() for v in range(256)}
    ends={v:f.variable() for v in x}
    f.exactly([-x[v] for v in sorted(old)],d)
    f.exactly([x[v] for v in x if v not in old],d)
    f.exactly(list(ends.values()),2)
    for v in x:
        adjacent=[x[u] for u in g.NEIGHBOURS[v]]
        f.clauses.append([-ends[v],x[v]])
        g.bounds(f,adjacent,1,2,[-x[v]])
        g.bounds(f,adjacent,0,1,[-ends[v]])
        g.bounds(f,adjacent,2,len(adjacent),[-x[v],ends[v]])
    g.face_bounds(f,x)
    for c in cycles:f.clauses.append(g.cycle_clause(x,c))
    for p in found:
        assert len(p)==99 and valid(p,8) and len(old-set(p))==d
        f.clauses.append([-x[v] for v in sorted(p)])
    return f,x

def components(chosen,g):
    unseen=set(chosen);pieces=[]
    while unseen:
        frontier=[min(unseen)];unseen.remove(frontier[0])
        for v in frontier:
            extra=set(g.NEIGHBOURS[v])&unseen;unseen-=extra;frontier.extend(sorted(extra))
        pieces.append(frontier)
    return pieces

def ordered(chosen,g):
    ends=sorted(v for v in chosen if len(chosen.intersection(g.NEIGHBOURS[v]))==1)
    assert len(ends)==2;p=[ends[0]];left=chosen-{p[0]}
    while left:
        u,=left.intersection(g.NEIGHBOURS[p[-1]]);p.append(u);left.remove(u)
    assert p[-1]==ends[-1] and valid(p,8);return p

def main():
    cli=ArgumentParser();cli.add_argument("action",choices=("solve","replay"))
    cli.add_argument("--radii",nargs="+",type=int,default=[1,2,3,4,5]);cli.add_argument("--seconds",type=float,default=15)
    a=cli.parse_args();h=hunt();g=h.rebuild.geometry;old=set(read(HERE/"input-arms.json")["known_endpoints"]["0"]["parent"])
    out=HERE/"site-distance.json";ledger=read(out) if out.exists() else {};paper=HERE/"proofs";paper.mkdir(exist_ok=True)
    with TemporaryDirectory(prefix="q9-sphere276-") as t:
        tmp=Path(t);tools=h.rebuild.masks.compilers(tmp);h.rebuild.masks.fixed.HERE=HERE
        for d in sorted(map(int,ledger)) if a.action=="replay" else a.radii:
            entry=ledger.setdefault(str(d),dict(cycles=[],paths=[]));cnf=tmp/"partner.cnf";trace=tmp/"sphere.lrat"
            stop=monotonic()+a.seconds
            if a.action=="solve" and entry.get("status")=="excluded":continue
            while True:
                form,x=encode(g,old,d,entry["cycles"],entry["paths"]);digest=form.save(cnf)
                if a.action=="replay":
                    assert digest==entry["cnf"] and len(form.clauses)==entry["clauses"]
                    if entry["status"]=="excluded":
                        pf=HERE/entry["proof"]
                        assert sha256(pf.read_bytes()).hexdigest()==entry["compressed"]
                        assert h.rebuild.masks.p.check_proof(cnf,pf,tools[0])==entry["replay"]
                    break
                entry.update(cnf=digest,clauses=len(form.clauses))
                trace.unlink(missing_ok=True)
                try:
                    proc=subprocess.run([str(g.SOLVER),"-q","--seed=1","--lrat","--no-binary",str(cnf),str(trace)],
                        capture_output=True,timeout=max(.1,stop-monotonic()))
                except subprocess.TimeoutExpired:
                    entry["status"]="open";save(out,ledger);break
                if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
                    z=paper/(digest+".lrat.gz");m=h.rebuild.masks
                    entry.update(status="excluded",proof=z.relative_to(HERE).as_posix(),raw=m.p.joins.archive(trace,z),compressed=m.digest(z))
                    entry["replay"]=m.p.check_proof(cnf,z,tools[0]);m.fixed.compact(tmp,*tools,entry);save(out,ledger);break
                if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:raise RuntimeError(proc.stderr[-500:])
                truth={int(v) for l in proc.stdout.splitlines() if l.startswith(b"v ") for v in l.split()[1:]}
                sites={v for v in x if x[v] in truth}
                assert len(sites)==99 and len(old-sites)==d
                pcs=components(sites,g)
                if len(pcs)==1:
                    p=ordered(sites,g);entry["paths"].append(p)
                else:
                    loops=[part for part in pcs if all(len(sites.intersection(g.NEIGHBOURS[v]))==2 for v in part)]
                    assert len(loops)==len(pcs)-1
                    for loop in loops:
                        g.cycle_clause(x,loop);entry["cycles"].append(sorted(loop))
            print(a.action,d,entry["status"],"labelled paths",len(entry["paths"]),"cycles",len(entry["cycles"]),flush=True)
    if a.action=="replay":
        count=0
        for r in range(1,100):
            if ledger.get(str(r),{}).get("status")!="excluded":break
            count=r
        save(HERE/"site-distance-replay.json",dict(ledger_sha256=sha256(out.read_bytes()).hexdigest(),complete_through=count,
            per_radius={t:dict(status=e["status"],labelled=len(e["paths"]),shapes=sorted({canonical(p) for p in e["paths"]})) for t,e in ledger.items()}))
if __name__=="__main__":main()
