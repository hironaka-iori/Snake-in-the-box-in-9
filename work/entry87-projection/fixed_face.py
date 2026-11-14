"""Unrestricted outside-face completion of an entire prescribed Q8 path."""
import argparse
from itertools import combinations
import json,gzip,shutil,subprocess
from pathlib import Path
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver,pysolvers
from partner93 import source_parent
from partner_cuts import abstract_cycles
from proof_ascii import write_ascii
from rerun_deep_certificate import digest
from solve import defects,save


def solve_face(parent,tag,budget,checker,static,desired=193):
    assert len(set(parent))==len(parent) and not defects(parent) and all(v<256 for v in parent)
    roots={parent[0],parent[-1]}
    count=desired-len(parent)
    allow=set(range(256))-(set(parent)-roots)
    graph={v:sorted(w for w in allow if (v^w).bit_count()==1) for v in sorted(allow)}
    pool=IDPool()
    use={v:pool.id(("selected",v)) for v in graph}
    end={v:pool.id(("end",v)) for v in graph}
    captured=[];prefix=Path("fixed-face-proof-"+tag)
    with Solver(name="cadical195",with_proof=checker is not None) as backend:
        def add(clause):
            backend.add_clause(clause)
            if checker is not None:captured.append(clause)
        def equal(lits,k):
            for clause in CardEnc.equals(lits,bound=k,vpool=pool,encoding=EncType.totalizer).clauses:add(clause)
        equal(list(use.values()),count)
        # Each unselected root copy leaves an endpoint on the fixed face.
        # Total endpoints=2 implies count(outer endpoints)=count(selected roots).
        equal([*end.values(),*[-use[v] for v in sorted(roots)]],2)
        add([use[v] for v in sorted(roots)])
        for x,adj in graph.items():
            v=use[x];e=end[x];ns=[use[y] for y in adj]
            add([-e,v])
            if x in roots:
                # Selecting a root copy forces a crossing to the fixed parent.
                add([-v,e,*ns])
                for a in ns:add([-e,-a])
                for a,b in combinations(ns,2):add([-v,-a,-b])
            else:
                add([-v,*ns])
                for a,b,c in combinations(ns,3):add([-v,-a,-b,-c])
                for a,b in combinations(ns,2):add([-e,-a,-b])
                for i in range(len(ns)):add([-v,e,*ns[:i],*ns[i+1:]])
        cuts=set()
        for dim in range(2,static+1):
            for dirs in combinations(range(8),dim):
                mask=sum(1<<b for b in dirs)
                positions=[sum(((n>>i)&1)<<b for i,b in enumerate(dirs)) for n in range(1<<dim)]
                for base in range(256):
                    if base&mask:continue
                    for cycle in cycle_types[dim]:
                        vertices=tuple(sorted(base|positions[c] for c in cycle))
                        if vertices in cuts or not set(vertices)<=allow:continue
                        assert all(len(set(graph[v]).intersection(vertices))==2 for v in vertices)
                        cuts.add(vertices);add([-use[v] for v in vertices])
        status="OPEN";witness=None;disconnected=[]
        while True:
            remaining=budget-backend.accum_stats()["conflicts"]
            if remaining<=0:break
            backend.conf_budget(remaining);answer=backend.solve_limited()
            if answer is not True:
                status="UNSAT" if answer is False else "OPEN";break
            pos=set(backend.get_model());chosen={v for v,k in use.items() if k in pos}
            full=set(parent)|{v|256 for v in chosen}
            assert len(full)==desired
            adjacent={v:{v^(1<<i) for i in range(9) if (v^(1<<i)) in full} for v in full}
            tips=[v for v in full if len(adjacent[v])==1]
            assert len(tips)==2 and all(len(ns) in (1,2) for ns in adjacent.values())
            path=[tips[0]];seen={tips[0]}
            while adjacent[path[-1]]-seen:
                nexts=adjacent[path[-1]]-seen;assert len(nexts)==1
                v=nexts.pop();path.append(v);seen.add(v)
            if len(path)==desired:
                assert not defects(path);witness=path;status="FOUND";break
            # Each other component is a closed cycle. Selecting all of its
            # mutable vertices forces that same cycle, even if other sites change.
            rest=full-seen
            while rest:
                root=rest.pop();cycle={root};stack=[root]
                while stack:
                    ns=adjacent[stack.pop()]&rest;rest-=ns;cycle|=ns;stack.extend(ns)
                assert all(len(adjacent[v]&cycle)==2 for v in cycle)
                outer=sorted(v^256 for v in cycle if v>=256)
                assert outer
                add([-use[v] for v in outer]);disconnected.append(outer)
        row=dict(tag=tag,parent=parent,desired=desired,allowed=len(allow),outside_count=count,
                 status=status,budget=budget,static_cycles=len(cuts),dimension_limit=static,
                 dynamic_cycles=disconnected,witness=witness,stats=backend.accum_stats())
        if checker and status=="UNSAT":
            formula=prefix.with_suffix(".cnf");proof=prefix.with_suffix(".drat");core=prefix.with_suffix(".core")
            with formula.open("w",newline="\n") as f:
                f.write(f"p cnf {max(abs(l) for c in captured for l in c)} {len(captured)}\n")
                for c in captured:f.write(" ".join(map(str,c))+" 0\n")
            s=backend.solver;pysolvers.flushpr(s.prfp);s.prfile.seek(0)
            with proof.open("wb") as f:write_ascii(s.prfile,f)
            for args in ([str(formula),str(proof),"-l",str(core)],[str(formula),str(core)]):
                proc=subprocess.run([str(checker),*args],capture_output=True)
                assert proc.returncode==0 and b"s VERIFIED" in proc.stdout.splitlines()
            row["checker"]=proc.stdout.decode(errors="replace").splitlines()[-10:]
            for file in (formula,core):
                row[file.suffix[1:]+"_sha256"]=digest(file)
                with file.open("rb") as src,Path(str(file)+".gz").open("wb") as dst:
                    with gzip.GzipFile(fileobj=dst,mode="wb",filename="",mtime=0,compresslevel=5) as gz:
                        shutil.copyfileobj(src,gz)
    suffix="-checked" if checker else ""
    save(Path("fixed-face-"+tag+suffix+".json"),row)
    print(tag,status,row["stats"]["conflicts"],len(disconnected),flush=True)
    return row


cycle_types={d:[c for c in abstract_cycles(d) if len(c)==2*d] for d in (2,3,4)}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=0);parser.add_argument("--stop",type=int,default=99)
    parser.add_argument("--budget",type=int,default=1200000)
    parser.add_argument("--checker",type=Path);parser.add_argument("--static",type=int,default=4)
    a=parser.parse_args();parent=source_parent()[a.start:a.stop]
    solve_face(parent,f"seed-{a.start}-{a.stop}",a.budget,a.checker.resolve() if a.checker else None,a.static)
