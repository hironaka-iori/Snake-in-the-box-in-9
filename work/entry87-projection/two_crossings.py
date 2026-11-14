"""Two crossings with a fixed 98-edge middle path in the opposite Q8 face."""
import argparse
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from partner93 import source_parent
from solve import defects,save


def run(budget,variant,extra,checker=None):
    parent=source_parent();a,b=parent[0],parent[-1];roots={a,b}
    allowed=sorted(set(range(256))-(set(parent)-roots));assert len(allowed)==159
    graph={v:sorted(w for w in allowed if (v^w).bit_count()==1) for v in allowed}
    pool=IDPool();sel={v:pool.id(("sel",v)) for v in allowed}
    end={v:pool.id(("end",v)) for v in allowed}
    encoder={"totalizer":EncType.totalizer,"network":EncType.cardnetwrk,"sequential":EncType.seqcounter}[variant]
    with Solver(name="cadical195",with_proof=checker is not None) as engine:
        captured=[]
        if checker is None:sat=engine
        else:
            class Capture:
                def add_clause(self,c):captured.append(c);engine.add_clause(c)
                def append_formula(self,cs):
                    for c in cs:self.add_clause(c)
                def __getattr__(self,k):return getattr(engine,k)
            sat=Capture()
        def equal(literals,k):
            sat.append_formula(CardEnc.equals(literals,bound=k,vpool=pool,encoding=encoder).clauses)
        for r in roots:sat.add_clause([sel[r]])
        equal(list(sel.values()),94);equal(list(end.values()),2)
        evens=[sel[v] for v in allowed if v.bit_count()%2==0]
        sat.append_formula(CardEnc.atleast(evens,bound=47,vpool=pool,encoding=encoder).clauses)
        sat.append_formula(CardEnc.atmost(evens,bound=48,vpool=pool,encoding=encoder).clauses)
        for v in allowed:
            e=end[v];s=sel[v];ns=[sel[w] for w in graph[v]]
            sat.add_clause([-e,s])
            if v in roots:
                # The extra crossing edge is always present. A global endpoint
                # at the root therefore has zero selected neighbours in this face.
                sat.add_clause([e,*ns])
                for y in ns:sat.add_clause([-e,-y])
                for x,y in combinations(ns,2):sat.add_clause([-x,-y])
            else:
                sat.add_clause([-s,*ns])
                for triple in combinations(ns,3):sat.add_clause([-s,*[-x for x in triple]])
                for x,y in combinations(ns,2):sat.add_clause([-e,-x,-y])
                for i in range(len(ns)):
                    sat.add_clause([-s,e,*ns[:i],*ns[i+1:]])
        # Independent of how the two arms divide their chosen vertices, every
        # cycle within this face is forbidden in the final path.
        from partner_cuts import abstract_cycles
        dims=(2,3,4) if extra else (2,3)
        seen=set();allow=set(allowed)
        for dim in dims:
            patterns=[c for c in abstract_cycles(dim) if len(c)==2*dim]
            for directions in combinations(range(8),dim):
                mask=sum(1<<j for j in directions)
                spread=[sum(((x>>i)&1)<<j for i,j in enumerate(directions)) for x in range(1<<dim)]
                for offset in range(256):
                    if offset&mask:continue
                    for c in patterns:
                        q=tuple(sorted(offset|spread[x] for x in c))
                        if q in seen or not set(q)<=allow:continue
                        assert all(len(set(graph[v]).intersection(q))==2 for v in q)
                        seen.add(q);sat.add_clause([-sel[v] for v in q])
        dynamic=[];witness=None;status="OPEN"
        while True:
            remain=budget-sat.accum_stats()["conflicts"]
            if remain<=0:break
            sat.conf_budget(remain);state=sat.solve_limited()
            if state is not True:
                status="UNSAT" if state is False else "OPEN";break
            positive=set(sat.get_model());chosen={v for v,l in sel.items() if l in positive}
            assert len(chosen)==94
            def component(start):
                group={start};stack=[start]
                while stack:
                    new=(chosen-group).intersection(graph[stack.pop()]);group|=new;stack.extend(new)
                return group
            A=component(a);B=component(b)
            if A==B:
                # These selected vertices already join the roots through the outer
                # face, creating a cycle with the full prescribed middle.
                sat.add_clause([-sel[v] for v in sorted(A)]);dynamic.append(sorted(A));continue
            rest=chosen-A-B
            if rest:
                # A rootless closed component can never be part of a path. An
                # endpoint-bearing stray component instead needs a boundary edge.
                C=component(min(rest))
                edge=set().union(*(set(graph[v]) for v in C))-C
                sat.add_clause([-sel[v] for v in C]+[sel[v] for v in sorted(edge)])
                dynamic.append(dict(component=sorted(C),boundary=sorted(edge)));continue
            def leg(root,C):
                path=[root]
                while len(path)<len(C):
                    nxt=(C-set(path)).intersection(graph[path[-1]])
                    assert len(nxt)==1
                    path.append(nxt.pop())
                return path
            left=leg(a,A);right=leg(b,B)
            witness=left[::-1]+[v|256 for v in parent]+right
            assert len(witness)==193 and not defects(witness)
            status="FOUND";break
        row=dict(status=status,budget=budget,encoding=variant,extra=extra,
                 stats=sat.accum_stats(),static_cycles=len(seen),dynamic=dynamic,witness=witness)
        if checker and status=="UNSAT":
            from proof_ascii import write_ascii
            from pysat.solvers import pysolvers
            from rerun_deep_certificate import digest
            import gzip,shutil,subprocess
            prefix=Path(f"two-crossings-proof-{variant}-{int(extra)}")
            cnf=prefix.with_suffix(".cnf");drat=prefix.with_suffix(".drat");core=prefix.with_suffix(".core")
            with cnf.open("w",newline="\n") as f:
                f.write(f"p cnf {max(abs(u) for c in captured for u in c)} {len(captured)}\n")
                for c in captured:f.write(" ".join(map(str,c))+" 0\n")
            backend=engine.solver;pysolvers.flushpr(backend.prfp);backend.prfile.seek(0)
            with drat.open("wb") as f:write_ascii(backend.prfile,f)
            for args in [[str(cnf),str(drat),"-l",str(core)],[str(cnf),str(core)]]:
                checked=subprocess.run([str(checker),*args],capture_output=True)
                assert checked.returncode==0 and b"s VERIFIED" in checked.stdout.splitlines()
            row["checker"]=checked.stdout.decode(errors="replace").splitlines()[-10:]
            for file in (cnf,core):
                row[file.suffix[1:]+"_sha256"]=digest(file)
                with file.open("rb") as src,Path(str(file)+".gz").open("wb") as dst:
                    with gzip.GzipFile(filename="",fileobj=dst,mode="wb",mtime=0,compresslevel=5) as gz:
                        shutil.copyfileobj(src,gz)
    tag="-checked" if checker else ""
    save(Path(f"two-crossings-{variant}-{int(extra)}{tag}.json"),row)
    print(status,row["stats"],len(dynamic),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--budget",type=int,default=3000000)
    parser.add_argument("--encoding",default="totalizer")
    parser.add_argument("--extra",action="store_true")
    parser.add_argument("--checker",type=Path)
    a=parser.parse_args();run(a.budget,a.encoding,a.extra,a.checker.resolve() if a.checker else None)
