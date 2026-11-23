"""Permit arbitrary changes inside a coordinate face; keep outside occupancy fixed."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from pysat.solvers import Minicard
from search_q9_wynn_plateau import verify

NB = [tuple(v^(1<<i) for i in range(9)) for v in range(512)]


def check_face(seed, free, target, budget, endpoint_parity=None):
    fixed=set(seed)-free
    assert fixed
    root=next(iter(fixed))
    inside={v:[u+1 for u in NB[v] if u in free] for v in free}
    endpoints=[]
    need_ends=2
    with Minicard() as solver:
        def exact(lits,n):
            if not 0<=n<=len(lits):
                solver.add_clause([])
            else:
                solver.add_atmost(lits,n)
                solver.add_atmost([-x for x in lits],len(lits)-n)
        exact([v+1 for v in free],target+1-len(fixed))
        if endpoint_parity is not None:
            assert target%2==0
            for color in (0,1):
                count=target//2+(color==endpoint_parity)
                count-=sum(v.bit_count()%2==color for v in fixed)
                exact([v+1 for v in free if v.bit_count()%2==color],count)
        for v in fixed:
            out=sum(u in fixed for u in NB[v])
            choices=[u+1 for u in NB[v] if u in free]
            assert len(choices)<=1
            if not choices:
                if out not in (1,2):return "UNSAT",None
                if out==1 and endpoint_parity is not None and v.bit_count()%2!=endpoint_parity:return "UNSAT",None
                need_ends-=out==1
            elif out==0:
                if endpoint_parity is not None and v.bit_count()%2!=endpoint_parity:return "UNSAT",None
                solver.add_clause(choices)
                need_ends-=1
            elif out==1:
                e=513+v
                if endpoint_parity is not None and v.bit_count()%2!=endpoint_parity:solver.add_clause([-e])
                solver.add_clause([e,choices[0]])
                solver.add_clause([-e,-choices[0]])
                endpoints.append(e)
            elif out==2:
                solver.add_clause([-choices[0]])
            else:
                return "UNSAT",None
        for v in free:
            x=v+1;e=513+v
            out=sum(u in fixed for u in NB[v])
            if out>2:
                solver.add_clause([-x])
                continue
            endpoints.append(e)
            if endpoint_parity is not None and v.bit_count()%2!=endpoint_parity:solver.add_clause([-e])
            solver.add_clause([-e,x])
            adj=inside[v]+[e]
            k=2-out
            for a in combinations(adj,k+1):
                solver.add_clause([-x,*(-u for u in a)])
            for a in combinations(adj,len(adj)-k+1):
                solver.add_clause([-x,*a])
        exact(endpoints,need_ends)
        solver.set_phases([v+1 for v in seed if v in free])
        while True:
            left=budget-solver.accum_stats()["conflicts"]
            if left<=0:return "UNKNOWN",None
            solver.conf_budget(left)
            status=solver.solve_limited()
            if status is not True:return ("UNKNOWN" if status is None else "UNSAT"),None
            model=set(solver.get_model())
            occupied=fixed|{v for v in free if v+1 in model}
            assert len(occupied)==target+1
            unseen=occupied.copy()
            components=[]
            while unseen:
                start=next(iter(unseen))
                comp={start}
                stack=[start];unseen.remove(start)
                while stack:
                    for u in NB[stack.pop()]:
                        if u in unseen:
                            unseen.remove(u);comp.add(u);stack.append(u)
                components.append(comp)
            if len(components)==1:
                ends=[v for v in occupied if len(set(NB[v])&occupied)==1]
                assert len(ends)==2
                path=[ends[0]];rest=occupied-{ends[0]}
                while rest:
                    opts=set(NB[path[-1]])&rest
                    assert len(opts)==1
                    u=opts.pop();rest.remove(u);path.append(u)
                assert verify(path)
                return "FOUND",path
            for comp in components:
                if root in comp:continue
                border={u+1 for v in comp for u in NB[v] if u in free-comp}
                # A fixed vertex in this component must reach root. Otherwise,
                # require an exit if one chosen representative stays selected.
                clause=sorted(border)
                if comp.isdisjoint(fixed):clause.append(-(min(comp)+1))
                solver.add_clause(clause)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("bank",type=Path)
    ap.add_argument("--dim",type=int,choices=range(2,9),default=7)
    ap.add_argument("--budget",type=int,default=10000)
    ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--count",type=int,default=1)
    ap.add_argument("--control",action="store_true")
    ap.add_argument("--report",type=argparse.FileType("x"))
    args=ap.parse_args()
    stats=Counter()
    bank=json.loads(args.bank.read_text())
    for index,row in enumerate(bank[args.start:args.start+args.count],args.start):
        p=row["vertex_sequence"]
        assert verify(p)
        for dims in combinations(range(9),9-args.dim):
            mask=sum(1<<d for d in dims)
            for base in range(512):
                if base&~mask:continue
                free={v for v in range(512) if v&mask==base}
                if args.control:
                    if p[-1] not in free:continue
                    status,w=check_face(p[:-1],free,191,args.budget)
                    if status=="FOUND":
                        print("verified 190 to 191",flush=True)
                        return
                else:
                    status,w=check_face(p,free,192,args.budget)
                    if args.report:
                        record=dict(seed=index,mask=mask,base=base,status=status)
                        if w is not None:record["vertices"]=w
                        print(json.dumps(record),file=args.report,flush=True)
                    if w is not None:
                        print(json.dumps(w),flush=True)
                        return
                stats[status]+=1
    print(dict(stats),flush=True)


if __name__=="__main__":
    main()
