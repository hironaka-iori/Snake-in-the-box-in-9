"""Decide attainment of a rooted 94-edge partner at each end of the five Q8 parents."""
from argparse import ArgumentParser
from itertools import permutations
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess

from survey import HERE, PREVIOUS, partner, save_json
from certify import archive


def joined(parent,path):
    if (len(parent)!=97 or len(path)!=95 or path[0]!=0 or path[-1]==0
            or sum(v.bit_count()%2==0 for v in path)!=48 or path[-1].bit_count()%2
            or set(parent)&set(path)!={0}):
        raise ValueError("Incorrect length, root, parity or projected intersection")
    complete=parent[::-1]+[256+v for v in path]
    partner.verify(parent,8)
    partner.verify(path,8)
    partner.verify(complete,9)
    return dict(partner=path,joined=complete,edges=len(complete)-1,
                checked_vertex_pairs=dict(parent=4656,partner=4465,joined=18336))


def rooted_map(source,target):
    """Cube isometry carrying the ordered source path to this rooted target."""
    if len(source)!=len(target):
        return
    image={}
    for u,v,a,b in zip(source,source[1:],target,target[1:]):
        s,t=u^v,a^b
        if s in image and image[s]!=t:
            return
        image[s]=t
    if len(image.values())!=len(set(image.values())):
        return
    masks={1<<j for j in range(8)}
    left,right=sorted(masks-set(image)),sorted(masks-set(image.values()))
    for rest in permutations(right):
        mapping=dict(image)
        mapping.update(zip(left,rest))
        values=[0]
        for j in range(8):
            values += [v^mapping[1<<j] for v in values]
        offset=values[source[0]]^target[0]
        values=[v^offset for v in values]
        if [values[v] for v in source]==target:
            yield values,offset,[mapping[1<<j] for j in range(8)]


def bank_controls(arms,raw):
    controls={(i,e):[] for i in sorted(arms) for e in (0,1)}
    for row in raw:
        count=0
        for (i,e),stored in controls.items():
            parent=partner.rooted_parent(arms[i],e)
            for lut,offset,axes in rooted_map(row["long"],parent):
                path=[lut[v] for v in row["short"]]
                stored.append(dict(seed=row["seed"],crossing_axis=row["axis"],
                                   translation=offset,axis_images=axes,**joined(parent,path)))
                count+=1
        if not count:
            raise ValueError("A recorded compatible pair did not transport")
    return controls


def donor_placement(parent,bank,seconds):
    """Try relative axis permutations; reject collisions as soon as their bits are assigned."""
    banned=set(parent[1:])
    deadline=monotonic()+seconds
    nodes=0
    completed=0
    for idx,source in enumerate(bank):
        if len(source["path"])!=95:
            continue
        for rev in (False,True):
            ordered=source["path"][::-1] if rev else source["path"]
            normalized=[v^ordered[0] for v in ordered]
            points=set(normalized)
            order=[]
            present=0
            groups=[]
            for depth in range(8):
                fresh=[i for i in range(8) if i not in order]
                def gain(j):
                    step=1<<j
                    return sum(bool(v&step) and not (v&~(present|step)) for v in points)
                axis=max(fresh,key=gain)
                order.append(axis)
                bit=1<<axis
                group=[sum(((v>>j)&1)<<k for k,j in enumerate(order[:-1]))
                       for v in points if v&bit and not v&~(present|bit)]
                groups.append(sorted(group))
                present|=bit
            def search(level,axes,lut,remaining):
                nonlocal nodes
                nodes+=1
                if level==8:
                    return list(axes)
                for t in remaining:
                    bit=1<<t
                    if any((lut[k]|bit) in banned for k in groups[level]):
                        continue
                    result=search(level+1,axes+[t],lut+[v|bit for v in lut],remaining-{t})
                    if result is not None:
                        return result
                return None
            if monotonic()>=deadline:
                return None,dict(completed_orientations=completed,partial_nodes=nodes,status="time_limit")
            assigned=search(0,[],[0],set(range(8)))
            if assigned is not None:
                images=[0]*8
                for j,t in zip(order,assigned):
                    images[j]=1<<t
                path=[sum(images[j] for j in range(8) if v & (1<<j)) for v in normalized]
                return dict(donor=idx,reversed=rev,source_root=ordered[0],axis_images=images,
                            **joined(parent,path)),dict(completed_orientations=completed,nodes=nodes,status="witness")
            completed+=1
    return None,dict(completed_orientations=completed,nodes=nodes,status="finished_library")


def encode94(parent,prefix=(0,),cycles=()):
    partner.validate_prefix(parent,prefix)
    cnf=partner.Formula()
    allowed=sorted(set(range(256))-set(parent[1:]))
    chosen={v:cnf.variable() for v in allowed}
    ends={v:cnf.variable() for v in allowed if v and v.bit_count()%2==0}
    cnf.exactly(list(ends.values()),1)
    for p,n in ((0,48),(1,47)):
        cnf.exactly([lit for v,lit in chosen.items() if v.bit_count()%2==p],n)
    for v,lit in chosen.items():
        ns=[chosen[w] for w in partner.NEIGHBOURS[v] if w in chosen]
        if v==0:
            partner.bounds(cnf,ns,1,1,[])
        elif v not in ends:
            partner.bounds(cnf,ns,2,2,[-lit])
        else:
            e=ends[v]
            cnf.clauses.append([-e,lit])
            partner.bounds(cnf,ns,1,2,[-lit])
            partner.bounds(cnf,ns,0,1,[-e])
            partner.bounds(cnf,ns,2,len(ns),[-lit,e])
    cnf.clauses.extend([chosen[v]] for v in prefix)
    for j,v in enumerate(prefix):
        if v in ends and j<94:
            cnf.clauses.append([-ends[v]])
        if j+1<len(prefix):
            required={prefix[j+1]}
            if j:
                required.add(prefix[j-1])
            cnf.clauses.extend([-chosen[w]] for w in partner.NEIGHBOURS[v] if w in chosen and w not in required)
    partner.face_bounds(cnf,chosen)
    for cycle in cycles:
        cnf.clauses.append(partner.cycle_clause(chosen,cycle))
    return cnf,chosen


def extract(parent,prefix,selected):
    if (len(selected)!=95 or sum(v.bit_count()%2==0 for v in selected)!=48
            or set(parent)&selected!={0} or not set(prefix)<=selected):
        raise ValueError("Incorrect SAT assignment")
    adj={v:selected.intersection(partner.NEIGHBOURS[v]) for v in selected}
    ends=sorted(v for v,ns in adj.items() if len(ns)==1)
    if (len(ends)!=2 or ends[0]!=0 or ends[1].bit_count()%2
            or any(len(adj[v])!=2 for v in selected-set(ends))):
        raise ValueError("Incorrect SAT degree assignment")
    path=[0]
    seen={0}
    while path[-1]!=ends[1]:
        onward=adj[path[-1]]-seen
        if len(onward)!=1:
            raise ValueError("Not a path component")
        path.append(onward.pop())
        seen.add(path[-1])
    if path[:len(prefix)]!=list(prefix):
        raise ValueError("Prefix mismatch")
    if seen==selected:
        return joined(parent,path),[]
    left=selected-seen
    cycles=[]
    while left:
        v=min(left)
        group=[v]
        left.remove(v)
        for v in group:
            more=sorted(adj[v]&left)
            left.difference_update(more)
            group+=more
        cycles.append(sorted(group))
    return None,cycles


def probe(parent,prefix,folder,exe,budget,tag):
    cnf,chosen=encode94(parent,prefix)
    formula,raw=folder/"case.cnf",folder/"case.lrat"
    start=monotonic()
    attempts=[]
    cycle_list=[]
    for flags in ([],["--plain"]):
        until=monotonic()+budget
        while monotonic()<until:
            h=cnf.save(formula)
            raw.unlink(missing_ok=True)
            rem=until-monotonic()
            if rem<=0:
                break
            entry=dict(flags=flags,cnf_sha256=h)
            attempts.append(entry)
            try:
                proc=subprocess.run([str(partner.SOLVER),"-q","--seed=1",*flags,"--lrat","--no-binary",
                                     str(formula),str(raw)],capture_output=True,timeout=rem)
            except subprocess.TimeoutExpired:
                entry["result"]="timeout"
                return dict(prefix=prefix,status="unknown",attempts=attempts)
            if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
                if not raw.is_file() or not raw.stat().st_size:
                    raise ValueError("Missing LRAT")
                proofdir=HERE/"endpoint94-proofs"
                proofdir.mkdir(exist_ok=True)
                target=proofdir/(tag+".lrat.gz")
                digest=archive(raw,target)
                regen,_=encode94(parent,prefix,cycle_list)
                if regen.save(formula)!=h:
                    raise ValueError("Regenerated proof instance differs")
                replay=subprocess.run([str(exe),str(formula),str(target)],capture_output=True,timeout=90)
                if replay.returncode==0 and replay.stdout.startswith(b"VERIFIED UNSAT "):
                    entry["result"]="verified_unsat"
                    return dict(prefix=prefix,status="verified_exclusion",attempts=attempts,
                                proof=target.relative_to(HERE).as_posix(),raw_proof_sha256=digest,
                                gzip_proof_sha256=partner.digest(target),cnf_sha256=h,cycles=cycle_list,
                                checker=replay.stdout.decode().strip(),seconds=monotonic()-start)
                entry["result"]="proof_not_replayed"
                break
            if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:
                raise RuntimeError((proc.returncode,proc.stderr[-300:]))
            truth={int(t) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                   for t in line.split()[1:] if int(t)>0}
            path,cycles=extract(parent,prefix,{v for v,lit in chosen.items() if lit in truth})
            if path:
                entry["result"]="verified_path"
                return dict(prefix=prefix,status="witness",attempts=attempts,**path)
            entry.update(result="disconnected",cycles=cycles)
            for cycle in cycles:
                cnf.clauses.append(partner.cycle_clause(chosen,cycle))
            cycle_list+=cycles
    return dict(prefix=prefix,status="unknown",attempts=attempts)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--seconds",type=float,default=9)
    cli.add_argument("--child-seconds",type=float,default=4)
    cli.add_argument("--donor-seconds",type=float,default=3)
    args=cli.parse_args()
    if min(args.seconds,args.child_seconds)<=0 or args.donor_seconds<0:
        cli.error("Invalid search budgets")
    comparison=partner.PREV/"comparison.json"
    donor_file=partner.PREV/"donors.json"
    checker=partner.PREV/"VerifyLrat.cs"
    compiler=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    bank=json.loads(donor_file.read_bytes())["shapes"]
    arms=partner.parent_arms()
    controls=bank_controls(arms,json.loads(comparison.read_bytes())["one_crossing_pairs"])
    files=[Path(__file__),HERE/"survey.py",HERE/"certify.py",PREVIOUS/"partner.py",partner.PREV/"free_outer.py",
           partner.SOURCE/"arc_sat.py",partner.PREV/"arm-structure.json",comparison,donor_file,checker,compiler,partner.SOLVER]
    pins={p.name:partner.digest(p) for p in files}
    dest=HERE/"endpoint94.json"
    data=json.loads(dest.read_bytes()) if dest.exists() else dict(pins=pins,records=[])
    if data["pins"]!=pins:
        raise ValueError("Checkpoint does not match current sources")
    with TemporaryDirectory(prefix="q8-end94-") as temp:
        folder=Path(temp)
        exe=folder/"VerifyLrat.exe"
        for (i,e),known in controls.items():
            parent=partner.rooted_parent(arms[i],e)
            row=next((r for r in data["records"] if r["case"]==[i,e]),None)
            if row is None:
                row=dict(case=[i,e],rooted_parent=parent,known_bank_witnesses=known,queries=[],status="open")
                data["records"].append(row)
            if row["status"]!="open":
                continue
            if known:
                row["status"]="bank_witness"
            elif not row.get("donor_witness"):
                donor,stats=donor_placement(parent,bank,args.donor_seconds)
                row["donor_scan"]=stats
                if donor:
                    row.update(status="donor_witness",donor_witness=donor)
            save_json(dest,data)
            if row["status"]=="open":
                if not exe.exists():
                    subprocess.run([str(compiler),"/nologo","/optimize+","/out:"+str(exe),str(checker)],
                                   capture_output=True,check=True,timeout=60)
                    data["checker_executable_sha256"]=partner.digest(exe)
                steps=partner.next_vertices(parent,[0])
                row["admissible_first_steps"]=steps
                prefixes=[[0]]+[[0,s] for s in steps]
                for prefix in prefixes:
                    previous=[r for r in row["queries"] if r["prefix"]==prefix]
                    if any(r["status"]=="verified_exclusion" for r in previous):
                        continue
                    tag=f"parent{i}-end{e}-"+"-".join(map(str,prefix))
                    result=probe(parent,prefix,folder,exe,args.seconds if len(prefix)==1 else args.child_seconds,tag)
                    row["queries"].append(result)
                    if result["status"]=="witness":
                        row["status"]="new_witness"
                    elif prefix==[0] and result["status"]=="verified_exclusion":
                        row["status"]="verified_exclusion"
                    save_json(dest,data)
                    if row["status"]!="open":
                        break
                if row["status"]=="open" and all(any(r["prefix"]==[0,s] and r["status"]=="verified_exclusion"
                                                    for r in row["queries"]) for s in steps):
                    row["status"]="verified_exclusion_by_first_steps"
            save_json(dest,data)
            print("parent",i,"endpoint",e,"archived joins",len(known),row["status"],flush=True)


if __name__=="__main__":
    main()
