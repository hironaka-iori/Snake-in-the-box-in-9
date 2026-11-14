"""Construct an exact rational feasible solution of the round-218 partner relaxation."""
import os
for variable in ("OPENBLAS_NUM_THREADS","OMP_NUM_THREADS","MKL_NUM_THREADS","NUMEXPR_NUM_THREADS"):
    os.environ[variable]="1"
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import subprocess
from partner93 import source_parent,PIN
from solve import save


def witness(root,denominator,minimum=94):
    p=source_parent()
    permitted=sorted(set(range(256))-(set(p)-{root}))
    idx={w:i for i,w in enumerate(permitted)}
    odd=[w for w in permitted if w.bit_count()%2]
    ep={w:len(permitted)+i for i,w in enumerate(odd)}
    n=len(permitted)+len(odd)
    U=[];E=[]
    def row(terms,rhs,eq=False):
        a=[0]*n
        for v,k in terms:a[v]+=k
        (E if eq else U).append((a,rhs))
    graph={w:[z for z in permitted if (w^z).bit_count()==1] for w in permitted}
    row([(idx[root],1)],1,True)
    row([(idx[x],1) for x in graph[root]],1,True)
    row([(v,1) for v in ep.values()],1,True)
    row([(idx[w],1 if w in ep else -1) for w in permitted],0,True)
    for w in permitted:
        if w==root:continue
        near=graph[w];d=len(near);e=[(ep[w],1)] if w in ep else []
        if e:row([(ep[w],1),(idx[w],-1)],0)
        row([(idx[w],2),*((j,-v) for j,v in e),*((idx[y],-1) for y in near)],0)
        row([(idx[w],d-2),*e,*((idx[y],1) for y in near)],d)
    shape=json.loads(subprocess.check_output(["git","show",PIN+":milestones/217-long-parent-search/data/complement-graph.json"]))
    r=next(a for a in shape["reports"] if a["root"]==root)
    for c in r["coordinate_squares"]+r["three_cube_induced_six_cycles"]:
        row([(idx[w],1) for w in c],len(c)-1)
    # First try a small fixed denominator. Integrality here chooses rational
    # grid points in the relaxation, not Boolean selections in the original graph.
    from ortools.sat.python import cp_model
    model=cp_model.CpModel()
    v=[model.new_int_var(0,denominator,f"v{i}") for i in range(n)]
    for aa,b in E:
        model.add(sum(q*v[j] for j,q in enumerate(aa) if q)==b*denominator)
    for aa,b in U:
        model.add(sum(q*v[j] for j,q in enumerate(aa) if q)<=b*denominator)
    model.add(sum(v[:len(permitted)])>=minimum*denominator)
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=30
    state=solver.solve(model)
    if state not in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        print(root,denominator,solver.status_name(state));return None
    point=[solver.value(z) for z in v]
    dot=lambda row:sum(a*b for a,b in zip(row,point))
    assert all(dot(row)==b*denominator for row,b in E)
    assert all(dot(row)<=b*denominator for row,b in U)
    total=sum(point[:len(permitted)])
    assert total>=minimum*denominator
    result=dict(root=root,denominator=denominator,selected_numerators={str(w):point[i] for w,i in idx.items()},
                endpoint_numerators={str(w):point[i] for w,i in ep.items()},total_numerator=total,
                inequalities=len(U),equalities=len(E))
    tag="" if minimum==94 else f"-atleast{minimum}"
    save(Path(f"partner-relax-{root}{tag}.json"),result)
    print(root,denominator,total,Counter(point[:len(permitted)]),flush=True)
    return result


if __name__=="__main__":
    import argparse
    a=argparse.ArgumentParser();a.add_argument("root",type=int);a.add_argument("denominator",type=int,default=5,nargs="?")
    a.add_argument("--minimum",type=int,default=94)
    arg=a.parse_args();witness(arg.root,arg.denominator,arg.minimum)
