"""Construct and verify feasible Q9 joins using one 47- and one 48-edge middle."""
from argparse import ArgumentParser
from collections import deque
from hashlib import sha256
from pathlib import Path
from random import Random
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess

from lifts import HERE, PREV, SOLVER, inspect, model, partners, verify
from positive_control import aligned_donors, pinned, recover

N = [tuple(v ^ (1 << i) for i in range(7)) for v in range(128)]
ALL = set(range(128))


def near_piece(mid, q, near, far, occupied):
    """Shortest admissible route from crossing to port; the other port is a singleton."""
    allowed = ALL - (set(mid)-{near}) - (occupied-{q}) - set(N[far]) - {far}
    if q not in allowed or near not in allowed or far in occupied:
        return None
    todo=deque([q])
    parent={q:None}
    while todo:
        v=todo.popleft()
        if v==near:
            route=[]
            while v is not None:
                route.append(v)
                v=parent[v]
            return route[::-1]
        for u in N[v]:
            if u in allowed and u not in parent:
                parent[u]=v
                todo.append(u)
    return None


def assembled(left, near, mid, tail):
    right=near+[128+v for v in mid]+tail
    return list(left[::-1])+[v+256 for v in right]


def grow_tail(far, available, budget, rng):
    """Keep the longest directly constructed induced extension of the far port."""
    best=[far]
    tail=[far]
    nodes=0
    def dfs(v, free):
        nonlocal nodes,best
        nodes+=1
        if len(tail)>len(best):
            best=tail.copy()
        if nodes>=budget or not free or len(tail)+len(free)<=len(best):
            return
        options=[u for u in N[v] if u in free]
        rng.shuffle(options)
        remaining=free-set(N[v])
        for u in options:
            if nodes>=budget:
                break
            tail.append(u)
            dfs(u,remaining)
            tail.pop()
    dfs(far,available-{far})
    return best


def heuristic(first, others, archived, save_witness, sites, stop, iteration):
    rng=Random(247+iteration)
    archived=list(archived)
    rng.shuffle(archived)
    # Try the longer bank arms first; endpoint trims permit a little more room.
    work=[(list(left[:-cut] if cut else left),i) for cut in (0,2,4,8,12)
          for i in range(len(others)) for left in archived]
    # Also construct both lower branches from their ports without a bank arm.
    fresh=[]
    for i,second in enumerate(others):
        qs=sorted(ALL-set(first[1:-1])-set(second[1:-1]))
        rng.shuffle(qs)
        for q in qs:
            for mid in (first,first[::-1]):
                near=near_piece(mid,q,mid[0],mid[-1],set())
                if near is not None:
                    fresh.append((near+[128+v for v in mid]+[mid[-1]],i))
    # A fresh construction establishes a baseline even if all archived
    # placements collide. Then prioritize long arms and revisit fresh sites.
    work=fresh[:10]+work+fresh
    examined=set()
    for left,i in work:
        if monotonic()>=stop:
            break
        key=tuple(left),i
        if key in examined:
            continue
        examined.add(key)
        q=left[0]
        if left[-1]>=128 or not any(u>=128 for u in left):
            continue
        lower={u for u in left if u<128}
        for mid in (others[i],others[i][::-1]):
            near=near_piece(mid,q,mid[0],mid[-1],lower)
            if near is None:
                continue
            banned=set(near)
            for v in near:
                banned.update(N[v])
            available=ALL-(set(mid)-{mid[-1]})-lower-banned
            if mid[-1] not in available:
                continue
            path=assembled(left,near,mid,[mid[-1]])
            save_witness(path,i,q,"two disjoint lower branches and a singleton far port")
            tail=grow_tail(mid[-1],available,1800,rng)
            path=assembled(left,near,mid,tail)
            save_witness(path,i,q,"bounded induced tail extension")
            sites[i,q]=max(sites.get((i,q),0),len(path)-1)


def native_query(mid,q,target,folder,budget,seed):
    cnf,chosen,fixed=model(mid,q,target)
    filename=folder/"mixed.cnf"
    deadline=monotonic()+budget
    tries=[]
    while monotonic()<deadline:
        digest=cnf.save(filename)
        remaining=deadline-monotonic()
        if remaining<=0:
            break
        row=dict(cnf_sha256=digest)
        tries.append(row)
        try:
            proc=subprocess.run([str(SOLVER),"--plain","-q","--seed="+str(seed),str(filename)],
                                capture_output=True,timeout=remaining)
        except subprocess.TimeoutExpired:
            row["outcome"]="time_limit"
            break
        if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
            row["outcome"]="no_witness_returned"
            break
        if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:
            raise RuntimeError((proc.returncode,proc.stderr[-400:]))
        positive={int(t) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                  for t in line.split()[1:] if int(t)>0}
        sel=fixed|{v for v,lit in chosen.items() if lit in positive}
        a,b=(sum(v>>8==x for v in sel)-1 for x in range(2))
        if a+b+1<target or max(a,b)>98:
            raise ValueError("Unexpected selected arm lengths")
        path,cycles=inspect(sel,mid,q,a,b)
        if path is not None:
            row["outcome"]="verified_path"
            return path,tries
        row.update(outcome="disconnected",cycles=len(cycles))
        cnf.clauses.extend([-chosen[v] for v in cycle if v in chosen] for cycle in cycles)
    return None,tries


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--seconds",type=float,default=32)
    args=cli.parse_args()
    if args.seconds<5:
        cli.error("At least five seconds are needed for construction and verification")
    start=monotonic()
    deadline=start+args.seconds
    first,others=partners()
    layout=json.loads((PREV/"middle.json").read_bytes())["layouts"][0]
    comparison=json.loads((PREV/"comparison.json").read_bytes())
    donors=aligned_donors(first,layout["middles"][1],comparison)
    archived=sorted({left for left,_ in donors},key=lambda p:(-len(p),p))
    files=[Path(__file__),HERE/"positive_control.py",HERE/"lifts.py",HERE/"complementary.json",
           PREV/"middle.json",PREV/"comparison.json",PREV/"ceiling.py",SOLVER]
    pins={p.name:sha256(p.read_bytes()).hexdigest() for p in files}
    dest=HERE/"mixed-witness.json"
    record=dict(pins=pins,runs=0,first_witness=None,best=None,queries=[])
    if dest.exists():
        record=json.loads(dest.read_bytes())
        if record["pins"]!=pins:
            raise ValueError("The checkpoint belongs to different sources or solver")
    record["runs"]+=1
    def checkpoint():
        tmp=dest.with_suffix(".tmp")
        tmp.write_text(json.dumps(record,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
        tmp.replace(dest)
    def save_witness(path,index,q,method):
        if record["best"] and len(path)-1<=record["best"]["edges"]:
            return
        observed,mids,lengths,pairs=recover(path)
        if observed!=q or any(m not in (list(w),list(w)[::-1]) for m,w in zip(mids,(first,others[index]))):
            raise ValueError("Wrong middle or crossing in candidate")
        rebuilt,cycles=inspect(set(path),mids,q,*lengths)
        if cycles or set(rebuilt)!=set(path):
            raise ValueError("Mixed witness failed the full induced-degree model")
        witness=dict(edges=len(path)-1,arms=lengths,middle_lengths=[47,48],partner=index,
                     q=q,all_pairs_checked=pairs,method=method,path=path)
        if record["first_witness"] is None:
            record["first_witness"]=witness
        record["best"]=witness
        record.pop("pinned_best",None)
        checkpoint()
        print("Verified mixed join",len(path)-1,"q",q,"partner",index,flush=True)
    sites={}
    heuristic(first,others,archived,save_witness,sites,start+min(7,args.seconds*0.26),record["runs"])
    if record["best"]:
        best=record["best"]
        sites[best["partner"],best["q"]]=best["edges"]
    ranked=sorted(sites,key=lambda k:(-sites[k],k))
    rng=Random(2470+record["runs"])
    other_sites=[(i,q) for i,mid in enumerate(others)
                 for q in sorted(ALL-set(first[1:-1])-set(mid[1:-1])) if (i,q) not in sites]
    rng.shuffle(other_sites)
    trials=(ranked+other_sites)[:8]
    with TemporaryDirectory(prefix="q9-mixed-example-") as temp:
        folder=Path(temp)
        for high in (False,True):
            for i,q in trials:
                current=record["best"]["edges"] if record["best"] else 95
                if current>=191 or monotonic()>deadline-3:
                    break
                target=min(191,max(current+1,188 if high else current+4))
                path,details=native_query([first,others[i]],q,target,folder,
                                          min(1.35,deadline-monotonic()-1),record["runs"])
                record["queries"].append(dict(partner=i,q=q,target=target,attempts=details))
                if path is not None:
                    save_witness(path,i,q,"native degree model and connectivity check")
                checkpoint()
        if record["best"] and "pinned_best" not in record:
            best=record["best"]
            control=pinned(best["path"],[first,others[best["partner"]]],folder)
            record["pinned_best"]={k:v for k,v in control.items() if k!="path"}
    record["last_run_seconds"]=monotonic()-start
    checkpoint()
    print("Longest verified mixed join",record["best"]["edges"] if record["best"] else None)


if __name__=="__main__":
    main()
