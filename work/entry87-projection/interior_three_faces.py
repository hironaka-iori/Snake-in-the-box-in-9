"""Replace an internal two-step segment by every induced four-step detour between its ends."""
import argparse
from pathlib import Path
from regrow_three_faces import key
from three_cross_faces import catalogue, decide
from solve import save


def detours(rows):
    initial={row["forest"] for row in rows}
    results={}
    for source,row in enumerate(rows):
        pair=row["forest"]
        for side in (0,1):
            path,other=pair[side],pair[1-side]
            all_vertices=set(path)|set(other)
            for i in range(len(path)-2):
                x,z,y=path[i:i+3]
                a,b=x^z,y^z
                assert a!=b and a.bit_count()==b.bit_count()==1
                kept=all_vertices-{z,x,y}
                forbidden=kept|{v^(1<<j) for v in kept for j in range(8)}
                for j in range(8):
                    c=1<<j
                    if c in (a,b):
                        continue
                    for step in (a,b):
                        bridge=(x^c,x^c^step,y^c)
                        if not forbidden.isdisjoint(bridge):
                            continue
                        new=path[:i+1]+bridge+path[i+2:]
                        shape=key(new,other)
                        if shape not in initial:
                            results.setdefault(shape,[]).append(dict(source=source,side=side,position=i,
                                                                     third_axis=j,first_middle_step=step))
    return [dict(forest=shape,edits=edits) for shape,edits in sorted(results.items())]


def general_detours(rows,span,gain):
    initial={row["forest"] for row in rows}
    results={}
    for source,row in enumerate(rows):
        for side in (0,1):
            path=row["forest"][side]; other=row["forest"][1-side]
            for i in range(len(path)-span):
                x,y=path[i],path[i+span]
                kept=set(path[:i]+path[i+span+1:]+other)
                blocked=kept|{v^(1<<j) for v in kept for j in range(8)}
                def walk(chain,remaining):
                    v=chain[-1]
                    if remaining==1:
                        if (v^y).bit_count()==1 and all((u^y).bit_count()>=2 for u in chain[:-1]):
                            new=path[:i]+chain+(y,)+path[i+span+1:]
                            if new!=path:
                                k=key(new,other)
                                if k not in initial:
                                    results.setdefault(k,[]).append(dict(source=source,side=side,position=i,bridge=chain+(y,)))
                        return
                    for bit in range(8):
                        w=v^(1<<bit)
                        if w in blocked or w==y or (w^y).bit_count()>remaining-1:
                            continue
                        if remaining>2 and (w^y).bit_count()<2:
                            continue
                        if all((w^u).bit_count()>=2 for u in chain[:-1]):
                            walk(chain+(w,),remaining-1)
                walk((x,),span+gain)
    return [dict(forest=k,edits=v) for k,v in sorted(results.items())]


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--stop",type=int,default=0)
    parser.add_argument("--budget",type=int,default=600000)
    parser.add_argument("--span",type=int,default=2)
    parser.add_argument("--gain",type=int,choices=(0,2),default=2)
    args=parser.parse_args()
    source=catalogue()
    rows=general_detours(source,args.span,args.gain)
    if (args.span,args.gain)==(2,2):
        assert {r["forest"] for r in rows}=={r["forest"] for r in detours(source)}
    tag=f"{args.span}-{args.gain}"
    if not args.stop:
        save(Path(f"three-interior-{tag}-menu.json"),rows)
        print(len(rows),sum(len(r["edits"]) for r in rows))
    for i in range(args.start,min(len(rows),args.stop)):
        decide(rows[i],f"interior-{tag}-{i}",193,args.budget)
