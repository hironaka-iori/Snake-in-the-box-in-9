"""Find a 93-edge Q8 partner compatible with the pinned 98-edge parent."""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import subprocess
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from solve import defects,save

PIN="8931c1efdf9397211b2047b7fea8e446c5d642d3"
HASH="2b328e537867b097316150be170a9af68e5af492bc7667d3b781b77d39e4e2f5"
GIT_HASH="58773f1c2c8e43272b7fd35140c443569595b5a70a5b323e47c1363253623fd1"


def source_parent():
    raw=subprocess.check_output(["git","show",PIN+":outputs/snake8_witness.json"])
    assert sha256(raw).hexdigest()==GIT_HASH
    assert sha256(raw.replace(b"\n",b"\r\n")).hexdigest()==HASH
    return json.loads(raw)["vertex_sequence"]


def search(root,budget,encoding,solver_name,first_step=None,first_cuts=False,checker=None,
           vertex_target=94,cycles=True,parent_path=None,label=None):
    parent=source_parent() if parent_path is None else list(parent_path)
    assert root in (parent[0],parent[-1]) and not defects(parent)
    if parent[-1]!=root:parent=parent[::-1]
    allowed=sorted(set(range(256))-(set(parent)-{root}))
    graph={v:[u for u in allowed if (u^v).bit_count()==1] for v in allowed}
    if parent_path is None:
        regions=json.loads(subprocess.check_output(["git","show",PIN+":milestones/217-long-parent-search/data/complement-graph.json"]))
        region=next(r for r in regions["reports"] if r["root"]==root)
        assert allowed==region["allowed_vertices"] and len(allowed)==158
    else:
        region=dict(coordinate_squares=[],three_cube_induced_six_cycles=[])
    pool=IDPool();var={v:pool.id(("select",v)) for v in allowed}
    opposite=[v for v in allowed if (v^root).bit_count()%2]
    same=[v for v in allowed if v not in opposite]
    eligible=opposite if vertex_target%2==0 else [v for v in same if v!=root]
    endpoint={v:pool.id(("end",v)) for v in eligible}
    encoder={"totalizer":EncType.totalizer,"network":EncType.cardnetwrk,"sequential":EncType.seqcounter}[encoding]
    prefix=Path("partner-proof-"+(str(root) if label is None else label))
    clauses=[]
    with Solver(name=solver_name,with_proof=checker is not None) as engine:
        if checker is None:sat=engine
        else:
            class Capture:
                def add_clause(self,c):
                    clauses.append(c);engine.add_clause(c)
                def append_formula(self,cs):
                    for c in cs:self.add_clause(c)
                def __getattr__(self,k):return getattr(engine,k)
            sat=Capture()
        sat.add_clause([var[root]])
        if first_step is not None:
            assert first_step in graph[root]
            sat.add_clause([var[first_step]])
        for part,number in ((same,(vertex_target+1)//2),(opposite,vertex_target//2)):
            sat.append_formula(CardEnc.equals([var[x] for x in part],bound=number,vpool=pool,encoding=encoder).clauses)
        end_literals=list(endpoint.values())
        sat.add_clause(end_literals)
        sat.append_formula(CardEnc.atmost(end_literals,bound=1,vpool=pool,encoding=EncType.seqcounter).clauses)
        for v in allowed:
            neighbours=[var[u] for u in graph[v]]
            current=var[v]
            # Degree is measured in the induced graph on all selected vertices.
            sat.add_clause([-current,*neighbours])
            for triple in combinations(neighbours,3):
                sat.add_clause([-current,*[-x for x in triple]])
            if v==root or v in endpoint:
                single=[-endpoint[v]] if v in endpoint else []
                if single:sat.add_clause([-endpoint[v],current])
                for a,b in combinations(neighbours,2):
                    sat.add_clause([-current,*single,-a,-b])
            if v!=root:
                cap=[endpoint[v]] if v in endpoint else []
                for i in range(len(neighbours)):
                    sat.add_clause([-current,*cap,*neighbours[:i],*neighbours[i+1:]])
        initial_cuts=[]
        for cycle in (region["coordinate_squares"]+region["three_cube_induced_six_cycles"] if cycles else []):
            vertices=set(cycle)
            assert len(vertices) in (4,6) and all(len(vertices.intersection(graph[v]))==2 for v in vertices)
            sat.add_clause([-var[v] for v in cycle]);initial_cuts.append(cycle)
        if first_cuts:
            from partner_cuts import add_subcube_cuts
            cuts=add_subcube_cuts(root,allowed,graph,var,sat)
        else:cuts=0
        dynamic=[]
        result=None
        while True:
            remaining=budget-sat.accum_stats()["conflicts"]
            if remaining<=0:break
            sat.conf_budget(remaining);result=sat.solve_limited()
            if result is not True:break
            model=set(sat.get_model())
            chosen={v for v,k in var.items() if k in model}
            assert len(chosen)==vertex_target
            unseen=set(chosen);components=[]
            while unseen:
                x=min(unseen);unseen.remove(x);part={x};stack=[x]
                while stack:
                    new=unseen.intersection(graph[stack.pop()]);unseen-=new;part|=new;stack.extend(new)
                components.append(part)
            extra=[c for c in components if root not in c]
            if not extra:
                path=[root];seen={root}
                while len(path)<vertex_target:
                    nexts=(chosen-seen).intersection(graph[path[-1]])
                    assert len(nexts)==1
                    head=nexts.pop();path.append(head);seen.add(head)
                assert not defects(path)
                snake=parent+[v|256 for v in path]
                assert len(snake)==len(parent)+vertex_target and not defects(snake)
                break
            # Components away from the specified endpoint must be cycles.
            for c in extra:
                assert all(len(c.intersection(graph[v]))==2 for v in c)
                sat.add_clause([-var[v] for v in sorted(c)]);dynamic.append(sorted(c))
            result=None
        r=dict(root=root,parent_sha256=HASH,budget=budget,encoding=encoding,solver=solver_name,
               status={True:"FOUND",False:"UNSAT",None:"OPEN"}[result],stats=sat.accum_stats(),
               static_cycle_cuts=len(initial_cuts),dynamic_cycles=dynamic)
        r.update(first_step=first_step,subcube_cuts=cuts)
        r.update(partner_vertices=vertex_target,parent_vertices=len(parent))
        if result is True:r.update(partner=path,vertices=snake)
        if checker and result is False:
            from pysat.solvers import pysolvers
            from proof_ascii import write_ascii
            from rerun_deep_certificate import digest
            import gzip,shutil
            # CaDiCaL's incremental proof is replayed against the union of all
            # original clauses and any subsequent cycle cuts, each geometrically valid.
            formula=prefix.with_suffix(".cnf");proof=prefix.with_suffix(".drat");core=prefix.with_suffix(".core")
            with formula.open("w",newline="\n") as f:
                f.write(f"p cnf {max(abs(l) for c in clauses for l in c)} {len(clauses)}\n")
                for c in clauses:f.write(" ".join(map(str,c))+" 0\n")
            backend=engine.solver;pysolvers.flushpr(backend.prfp);backend.prfile.seek(0)
            with proof.open("wb") as f:write_ascii(backend.prfile,f)
            for arguments in ([str(formula),str(proof),"-l",str(core)],[str(formula),str(core)]):
                replay=subprocess.run([str(checker),*arguments],capture_output=True)
                assert replay.returncode==0 and b"s VERIFIED" in replay.stdout.splitlines()
            r["checker"]=replay.stdout.decode(errors="replace").splitlines()[-10:]
            for f in (formula,core):
                r[f.suffix[1:]+"_sha256"]=digest(f)
                with f.open("rb") as src,Path(str(f)+".gz").open("wb") as dst:
                    with gzip.GzipFile(filename="",fileobj=dst,mode="wb",mtime=0,compresslevel=5) as gz:
                        shutil.copyfileobj(src,gz)
    suffix=(f"-first{first_step}" if first_step is not None else "")+("-faces" if first_cuts else "")
    if checker:suffix+="-checked"
    if vertex_target!=94:suffix+=f"-vertices{vertex_target}"
    if not cycles:suffix+="-nostatic"
    tag=root if label is None else label
    save(Path(f"partner93-{tag}-{encoding}-{solver_name}{suffix}.json"),r)
    print(root,r["status"],r["stats"],len(dynamic),flush=True)
    return r


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("root",type=int,choices=(0,78))
    parser.add_argument("--budget",type=int,default=3500000)
    parser.add_argument("--encoding",choices=("totalizer","network","sequential"),default="totalizer")
    parser.add_argument("--solver",default="cadical195")
    parser.add_argument("--first-step",type=int)
    parser.add_argument("--face-cuts",action="store_true")
    parser.add_argument("--checker",type=Path)
    parser.add_argument("--vertices",type=int,default=94)
    parser.add_argument("--no-static",action="store_true")
    a=parser.parse_args();search(a.root,a.budget,a.encoding,a.solver,a.first_step,a.face_cuts,
                                a.checker.resolve() if a.checker else None,a.vertices,not a.no_static)
