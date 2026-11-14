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


def search(root,budget,encoding,solver_name):
    parent=source_parent()
    assert len(parent)==99 and set((parent[0],parent[-1]))=={0,78} and not defects(parent)
    if parent[-1]!=root:parent=parent[::-1]
    allowed=sorted(set(range(256))-(set(parent)-{root}))
    graph={v:[u for u in allowed if (u^v).bit_count()==1] for v in allowed}
    regions=json.loads(subprocess.check_output(["git","show",PIN+":milestones/217-long-parent-search/data/complement-graph.json"]))
    region=next(r for r in regions["reports"] if r["root"]==root)
    assert allowed==region["allowed_vertices"] and len(allowed)==158
    pool=IDPool();var={v:pool.id(("select",v)) for v in allowed}
    opposite=[v for v in allowed if (v^root).bit_count()%2]
    same=[v for v in allowed if v not in opposite]
    endpoint={v:pool.id(("end",v)) for v in opposite}
    encoder={"totalizer":EncType.totalizer,"network":EncType.cardnetwrk,"sequential":EncType.seqcounter}[encoding]
    with Solver(name=solver_name) as sat:
        sat.add_clause([var[root]])
        for part in (same,opposite):
            sat.append_formula(CardEnc.equals([var[x] for x in part],bound=47,vpool=pool,encoding=encoder).clauses)
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
        for cycle in region["coordinate_squares"]+region["three_cube_induced_six_cycles"]:
            vertices=set(cycle)
            assert len(vertices) in (4,6) and all(len(vertices.intersection(graph[v]))==2 for v in vertices)
            sat.add_clause([-var[v] for v in cycle]);initial_cuts.append(cycle)
        dynamic=[]
        result=None
        while True:
            remaining=budget-sat.accum_stats()["conflicts"]
            if remaining<=0:break
            sat.conf_budget(remaining);result=sat.solve_limited()
            if result is not True:break
            chosen={v for v,k in var.items() if k in set(sat.get_model())}
            assert len(chosen)==94
            unseen=set(chosen);components=[]
            while unseen:
                x=min(unseen);unseen.remove(x);part={x};stack=[x]
                while stack:
                    new=unseen.intersection(graph[stack.pop()]);unseen-=new;part|=new;stack.extend(new)
                components.append(part)
            extra=[c for c in components if root not in c]
            if not extra:
                path=[root];seen={root}
                while len(path)<94:
                    nexts=(chosen-seen).intersection(graph[path[-1]])
                    assert len(nexts)==1
                    head=nexts.pop();path.append(head);seen.add(head)
                assert not defects(path)
                snake=parent+[v|256 for v in path]
                assert len(snake)==193 and not defects(snake)
                break
            # Components away from the specified endpoint must be cycles.
            for c in extra:
                assert all(len(c.intersection(graph[v]))==2 for v in c)
                sat.add_clause([-var[v] for v in sorted(c)]);dynamic.append(sorted(c))
            result=None
        r=dict(root=root,parent_sha256=HASH,budget=budget,encoding=encoding,solver=solver_name,
               status={True:"FOUND",False:"UNSAT",None:"OPEN"}[result],stats=sat.accum_stats(),
               static_cycle_cuts=len(initial_cuts),dynamic_cycles=dynamic)
        if result is True:r.update(partner=path,vertices=snake)
    save(Path(f"partner93-{root}-{encoding}-{solver_name}.json"),r)
    print(root,r["status"],r["stats"],len(dynamic),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("root",type=int,choices=(0,78))
    parser.add_argument("--budget",type=int,default=3500000)
    parser.add_argument("--encoding",choices=("totalizer","network","sequential"),default="totalizer")
    parser.add_argument("--solver",default="cadical195")
    a=parser.parse_args();search(a.root,a.budget,a.encoding,a.solver)
