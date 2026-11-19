"""Bound opposite-end partner lengths from above by exclusions and below by explicit paths."""
from argparse import ArgumentParser
from pathlib import Path
from random import Random
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess

from certify import archive
from survey import HERE, PREVIOUS, partner, save_json


def witness(parent,path,n):
    if (len(parent)!=97 or len(path)!=n+1 or not path or path[0]!=0
            or set(parent)&set(path)!={0} or sum(v.bit_count()%2==0 for v in path)!=n//2+1
            or path[-1].bit_count()%2!=n%2):
        raise ValueError("Invalid partner size, root, parity or parent intersection")
    lift=parent[::-1]+[256+v for v in path]
    partner.verify(parent,8)
    partner.verify(path,8)
    partner.verify(lift,9)
    return dict(partner_edges=n,joined_edges=n+97,partner=path,joined=lift,
                all_pairs=dict(parent=4656,partner=len(path)*n//2,joined=len(lift)*(len(lift)-1)//2))


def encode(parent,n,prefix=(0,),cycles=()):
    partner.validate_prefix(parent,prefix)
    if not 1<=n<=93 or len(prefix)>n+1:
        raise ValueError("Invalid target or prefix")
    cnf=partner.Formula()
    chosen={v:cnf.variable() for v in range(256) if v not in parent[1:]}
    ends={v:cnf.variable() for v in chosen if v!=0 and v.bit_count()%2==n%2}
    cnf.exactly(list(ends.values()),1)
    for parity,quota in ((0,n//2+1),(1,(n+1)//2)):
        cnf.exactly([lit for v,lit in chosen.items() if v.bit_count()%2==parity],quota)
    for v,lit in chosen.items():
        ns=[chosen[w] for w in partner.NEIGHBOURS[v] if w in chosen]
        if v==0:
            partner.bounds(cnf,ns,1,1,[])
        elif v in ends:
            e=ends[v]
            cnf.clauses.append([-e,lit])
            partner.bounds(cnf,ns,1,2,[-lit])
            partner.bounds(cnf,ns,0,1,[-e])
            partner.bounds(cnf,ns,2,len(ns),[-lit,e])
        else:
            partner.bounds(cnf,ns,2,2,[-lit])
    cnf.clauses.extend([chosen[v]] for v in prefix)
    for j,v in enumerate(prefix):
        if v in ends and j<n:
            cnf.clauses.append([-ends[v]])
        if j+1<len(prefix):
            permitted={prefix[j+1]}
            if j:
                permitted.add(prefix[j-1])
            cnf.clauses.extend([-chosen[w]] for w in partner.NEIGHBOURS[v] if w in chosen and w not in permitted)
    partner.face_bounds(cnf,chosen)
    for cycle in cycles:
        cnf.clauses.append(partner.cycle_clause(chosen,cycle))
    return cnf,chosen


def extract(parent,n,prefix,selected):
    if (len(selected)!=n+1 or not set(prefix)<=selected or set(parent)&selected!={0}
            or sum(v.bit_count()%2==0 for v in selected)!=n//2+1):
        raise ValueError("Incorrect model cardinality or parent avoidance")
    adj={v:selected.intersection(partner.NEIGHBOURS[v]) for v in selected}
    ends=sorted(v for v,ns in adj.items() if len(ns)==1)
    if (len(ends)!=2 or ends[0]!=0 or ends[1].bit_count()%2!=n%2
            or any(len(adj[v])!=2 for v in selected-set(ends))):
        raise ValueError("Incorrect induced degrees")
    path=[0]
    seen={0}
    while path[-1]!=ends[1]:
        avail=adj[path[-1]]-seen
        if len(avail)!=1:
            raise ValueError("Invalid endpoint component")
        path.append(avail.pop())
        seen.add(path[-1])
    if path[:len(prefix)]!=list(prefix):
        raise ValueError("Wrong ordered prefix")
    if seen==selected:
        return witness(parent,path,n),[]
    left=selected-seen
    cycles=[]
    while left:
        group=[min(left)]
        left.remove(group[0])
        for v in group:
            add=sorted(adj[v]&left)
            left.difference_update(add)
            group.extend(add)
        cycles.append(sorted(group))
    return None,cycles


def donor_bound(parent,donors,seconds):
    """Transport rooted prefixes, pruning a partially fixed isometry at its earliest collision."""
    blocked=set(parent[1:])
    best=[0]
    source=None
    nodes=0
    deadline=monotonic()+seconds
    # Prioritize the 94-edge sources, then 93; either orientation may give a long prefix.
    order=sorted((k for k,p in enumerate(donors) if len(p["path"]) in (94,95)),key=lambda k:-len(donors[k]["path"]))
    for k in order:
        for rev in (False,True):
            if monotonic()>=deadline:
                return best,dict(donor=source,nodes=nodes,stopped="time_limit")
            path=donors[k]["path"][::-1] if rev else donors[k]["path"]
            seq=[v^path[0] for v in path]
            # Label coordinates in first-transition order; early vertices then
            # have determined images at shallow permutation-tree levels.
            axes=list(dict.fromkeys((v^w).bit_length()-1 for v,w in zip(seq,seq[1:])))
            axes += [a for a in range(8) if a not in axes]
            vals=[sum(((v>>a)&1)<<i for i,a in enumerate(axes)) for v in seq]
            layers=[[(i,v^(1<<d)) for i,v in enumerate(vals) if v.bit_length()==d+1] for d in range(8)]
            def visit(d,table,rest,limit,used):
                nonlocal nodes,best,source
                nodes+=1
                if d==8:
                    best=[table[z] for z in vals[:limit]]
                    source=dict(shape=k,reversed=rev,original_root=path[0],source_axes=axes,image_axes=used)
                    return
                for axis in rest:
                    bit=1<<axis
                    stop=limit
                    for pos,sub in layers[d]:
                        if pos>=stop:
                            break
                        if table[sub]|bit in blocked:
                            stop=pos
                            break
                    if stop>len(best):
                        visit(d+1,table+[z|bit for z in table],rest-{axis},stop,used+[axis])
            visit(0,[0],set(range(8)),len(seq),[])
    return best,dict(donor=source,nodes=nodes,stopped="library_complete")


def improve_seed(parent,initial,seconds,seed):
    """Constructive endpoint regrowth only. No exclusion follows from its budget."""
    rng=Random(seed)
    blocked=set(parent[1:])
    best=list(initial)
    stop=monotonic()+seconds
    restarts=0
    while monotonic()<stop:
        restarts+=1
        keep=rng.randint(1,len(best))
        path=best[:keep]
        free=set(range(256))-blocked-set(path)
        for v in path[:-1]:
            free.difference_update(partner.NEIGHBOURS[v])
        while True:
            moves=sorted(free.intersection(partner.NEIGHBOURS[path[-1]]))
            if not moves:
                break
            free.difference_update(partner.NEIGHBOURS[path[-1]])
            if rng.random()<0.65:
                moves.sort(key=lambda t: (len(free.intersection(partner.NEIGHBOURS[t])),rng.random()))
                viable=[t for t in moves if free.intersection(partner.NEIGHBOURS[t])]
                nxt=viable[0] if viable else moves[0]
            else:
                nxt=rng.choice(moves)
            path.append(nxt)
        if len(path)>len(best):
            best=path
    return best,restarts


def decide(parent,n,prefix,folder,exe,seconds,tag,seed=1):
    cycles=[]
    cnf,chosen=encode(parent,n,prefix)
    model,raw=folder/"case.cnf",folder/"case.lrat"
    attempts=[]
    for flags in ([],["--plain"]):
        deadline=monotonic()+seconds
        while monotonic()<deadline:
            digest=cnf.save(model)
            raw.unlink(missing_ok=True)
            remaining=deadline-monotonic()
            if remaining<=0:
                break
            entry=dict(cnf_sha256=digest,flags=flags,seed=seed)
            attempts.append(entry)
            try:
                proc=subprocess.run([str(partner.SOLVER),"-q","--seed="+str(seed),*flags,"--lrat","--no-binary",
                                     str(model),str(raw)],capture_output=True,timeout=remaining)
            except subprocess.TimeoutExpired:
                entry["outcome"]="timeout"
                return dict(status="unknown",prefix=prefix,attempts=attempts)
            if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
                if not raw.is_file() or not raw.stat().st_size:
                    raise ValueError("Missing solver proof")
                out=HERE/"opposite-proofs"
                out.mkdir(exist_ok=True)
                proof=out/(tag+".lrat.gz")
                raw_hash=archive(raw,proof)
                rebuilt,_=encode(parent,n,prefix,cycles)
                if rebuilt.save(model)!=digest:
                    raise ValueError("Formula regeneration differs")
                checked=subprocess.run([str(exe),str(model),str(proof)],capture_output=True,timeout=90)
                if checked.returncode==0 and checked.stdout.startswith(b"VERIFIED UNSAT "):
                    entry["outcome"]="verified_unsat"
                    return dict(status="verified_exclusion",prefix=prefix,attempts=attempts,cycles=cycles,
                                cnf_sha256=digest,proof=proof.relative_to(HERE).as_posix(),raw_sha256=raw_hash,
                                gzip_sha256=partner.digest(proof),checker=checked.stdout.decode().strip())
                entry["outcome"]="proof_not_replayed"
                break
            if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:
                raise RuntimeError((proc.returncode,proc.stderr[-400:]))
            truth={int(t) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                   for t in line.split()[1:] if int(t)>0}
            found,new=extract(parent,n,prefix,{v for v,lit in chosen.items() if lit in truth})
            if found:
                entry["outcome"]="verified_witness"
                return dict(status="witness",prefix=prefix,attempts=attempts,**found)
            entry.update(outcome="disconnected",cycles=new)
            for cycle in new:
                cnf.clauses.append(partner.cycle_clause(chosen,cycle))
            cycles+=new
    return dict(status="unknown",prefix=prefix,attempts=attempts)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--seconds",type=float,default=9,help="Solver seconds for a full length query")
    cli.add_argument("--child-seconds",type=float,default=4,help="Solver seconds for each first-step fallback")
    cli.add_argument("--parent-seconds",type=float,default=42,help="Wall-time budget per opposite endpoint")
    cli.add_argument("--donor-seconds",type=float,default=1.0)
    cli.add_argument("--growth-seconds",type=float,default=0.6)
    cli.add_argument("--class-id",type=int,help="Run only this one saved parent")
    args=cli.parse_args()
    if min(args.seconds,args.child_seconds,args.parent_seconds)<=0 or min(args.donor_seconds,args.growth_seconds)<0:
        cli.error("Invalid budgets")
    previous=HERE/"endpoint94.json"
    prior=json.loads(previous.read_bytes())
    checker=partner.PREV/"VerifyLrat.cs"
    compiler=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    donorfile=partner.PREV/"donors.json"
    donors=json.loads(donorfile.read_bytes())["shapes"]
    arms=partner.parent_arms()
    if args.class_id is not None and args.class_id not in arms:
        cli.error("Unknown parent class")
    inputs=[Path(__file__),HERE/"certify.py",HERE/"survey.py",PREVIOUS/"partner.py",partner.PREV/"free_outer.py",
            partner.SOURCE/"arc_sat.py",partner.PREV/"arm-structure.json",partner.PREV/"comparison.json",
            previous,donorfile,checker,compiler,partner.SOLVER]
    pins={p.name:partner.digest(p) for p in inputs}
    dest=HERE/"opposite.json"
    data=json.loads(dest.read_bytes()) if dest.exists() else dict(pins=pins,records=[])
    if data["pins"]!=pins:
        raise ValueError("Checkpoint source or parent family differs")
    with TemporaryDirectory(prefix="q8-opposite-") as tmp:
        folder=Path(tmp)
        exe=folder/"VerifyLrat.exe"
        subprocess.run([str(compiler),"/nologo","/optimize+","/out:"+str(exe),str(checker)],
                       capture_output=True,check=True,timeout=60)
        data["checker_executable_sha256"]=partner.digest(exe)
        for i in sorted(arms):
            if args.class_id is not None and i!=args.class_id:
                continue
            old=next(r for r in prior["records"] if r["case"]==[i,1])
            if old["status"]!="verified_exclusion":
                raise ValueError("Missing full endpoint-1 upper exclusion at length 94")
            cert=next(r for r in old["queries"] if r["prefix"]==[0] and r["status"]=="verified_exclusion")
            if (not cert["checker"].startswith("VERIFIED UNSAT ") or
                    partner.digest(HERE/cert["proof"])!=cert["gzip_proof_sha256"]):
                raise ValueError("Prior replay or proof hash mismatch")
            parent=partner.rooted_parent(arms[i],1)
            if old["rooted_parent"]!=parent:
                raise ValueError("Different rooted parent")
            row=next((r for r in data["records"] if r["class_id"]==i),None)
            if row is not None and row["status"]=="exact":
                continue
            deadline=monotonic()+args.parent_seconds
            if row is None:
                path,scan=donor_bound(parent,donors,args.donor_seconds)
                path,restarts=improve_seed(parent,path,args.growth_seconds,248+i)
                if len(path)>94:
                    raise ValueError("Verified construction would contradict the preceding upper exclusion")
                low=witness(parent,path,len(path)-1)
                row=dict(class_id=i,endpoint=1,upper=93,lower=len(path)-1,status="open",
                         inherited_94_cnf=cert["cnf_sha256"],inherited_94_proof=cert["raw_proof_sha256"],
                         lower_witness=low,donor_search=scan,growth_restarts=restarts,length_queries={})
                data["records"].append(row)
                save_json(dest,data)
            while row["lower"]<row["upper"] and monotonic()<deadline:
                n=row["upper"]
                queries=row["length_queries"].setdefault(str(n),[])
                done={tuple(t["prefix"]) for t in queries if t["status"]=="verified_exclusion"}
                steps=partner.next_vertices(parent,[0])
                candidates=[[0]]+[[0,s] for s in steps]
                for prefix in candidates:
                    if tuple(prefix) in done:
                        continue
                    remaining=deadline-monotonic()
                    if remaining<=0:
                        break
                    budget=min(args.seconds if len(prefix)==1 else args.child_seconds,remaining)
                    tag=f"arm{i}-e1-length{n}-"+"-".join(map(str,prefix))
                    seed=1+sum(t["prefix"]==prefix for t in queries)
                    trial=decide(parent,n,prefix,folder,exe,budget,tag,seed)
                    queries.append(trial)
                    if trial["status"]=="witness":
                        row.update(lower=n,lower_witness={k:trial[k] for k in
                                   ("partner_edges","joined_edges","partner","joined","all_pairs")})
                    elif trial["status"]=="verified_exclusion":
                        done.add(tuple(prefix))
                    if (0,) in done or all((0,s) in done for s in steps):
                        row["upper"]=n-1
                    save_json(dest,data)
                    if row["lower"]==n or row["upper"]<n:
                        break
                if row["upper"]==n and row["lower"]<n:
                    break
            row["status"]="exact" if row["lower"]==row["upper"] else "open"
            save_json(dest,data)
            print("class",i,"opposite endpoint",row["lower"],row["upper"],row["status"],flush=True)


if __name__=="__main__":
    main()
