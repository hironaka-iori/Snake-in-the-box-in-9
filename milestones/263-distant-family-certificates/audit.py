"""Rebuild family formulas, verify proofs and compute exact coverage per rooted parent."""
from collections import Counter,defaultdict
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from family import HERE,MS,load,save,digest,bank,p,groups,sources,setup,compilers,replay

def extensions(path):
    for order in (path,path[::-1]):
        for v in p.joins.partner.NEIGHBOURS[order[-1]]:
            if v not in order and all((u^v).bit_count()!=1 for u in order[:-1]):
                yield order+[v]

def check_table(extra,negative):
    base=sorted(set().union(*(set(x) for x in extra)))
    def packed(x): return sum(1<<base.index(v) for v in x)
    terms=list(map(packed,extra))
    forbidden=list(map(packed,negative))
    for s in range(1<<len(base)):
        if any(s&m==0 for m in terms)==any(s&m==m for m in forbidden):
            raise ValueError("Transversal clauses disagree with explicit choice of parent")
    return 1<<len(base)

def main():
    old,pins=sources()
    maps=list(bank.permutation_images())
    pool=groups()
    data=load(HERE/"decisions.json")
    last=MS/"257-three-exchange-parents"
    before=load(last/"summary.json")
    known={r["shape"]+":"+str(r["end"]) for r in load(last/"partner-replay-95.json")["roots"] if r["status"]=="excluded"}
    certified=load(MS/"262-common-forbidden-sites/transfer.json")["covered"]
    roots=defaultdict(set)
    all_tags={k for g in pool.values() for k in g}
    for k in all_tags.intersection(known|set(certified)): roots[k].add((0,))
    tables={}
    evidence={}
    freq=Counter()
    best=None
    files=set()
    with TemporaryDirectory() as d:
        temp=Path(d)
        checker=compilers(temp)[0]
        for label,entry in sorted(data.items()):
            info=entry["description"]
            targets=pool[int(label.split(".")[0])]
            tags=info["members"]
            if not set(tags)<=set(targets): raise ValueError("Unlisted endpoint")
            blocked,extra,neg,pos,build=setup(tags,targets,old,maps)
            expected={f.relative_to(MS).as_posix():digest(f) for f in pins}
            if (sorted(blocked),extra,neg,pos,expected)!=(info["blocked"],info["extra"],info["negative"],info["positive"],info["source_pins"]):
                raise ValueError("Cut geometry differs")
            tables[label]=check_table(extra,neg)
            if entry.get("inherited"):
                if not any(not rule["sites"] for rule in pos): raise ValueError("Missing inherited proof")
                for k in tags: roots[k].add((0,))
            excluded=[]
            for key,row in entry["queries"].items():
                prefix=tuple(map(int,key.split(",")))
                if list(prefix)!=row["prefix"]: raise ValueError("Wrong prefix")
                replay(HERE,temp,checker,row,builder=build)
                freq[row["status"]]+=1
                if row["status"]=="excluded":
                    files.add(row["proof"])
                    excluded.append(prefix)
                    for k in tags: roots[k].add(prefix)
                if row["status"]=="witness":
                    for k,P in targets.items():
                        if set(row["path"])&P: continue
                        seq=load(last/"partner-input.json")["shapes"][k.split(":")[0]]
                        if k.endswith(":1"): seq=seq[::-1]
                        parent=[v^seq[0] for v in seq]
                        joined=parent[::-1]+[v+256 for v in row["path"]]
                        best=dict(vertices=joined,edges=len(joined)-1,pairs=bank.check_path(joined,9))
            evidence[label]=dict(members=len(tags),common_sites=len(blocked),negative_clauses=len(neg),
                                 positive_clauses=len(pos),excluded_prefixes=excluded,inherited=entry.get("inherited",False))
    summary={}
    for physical,targets in pool.items():
        for k,F in targets.items():
            prefix=[0]
            possible=p.joins.partner.next_vertices([0]+sorted(F),prefix)
            open_steps=[v for v in possible if (0,) not in roots[k] and (0,v) not in roots[k]]
            summary[k]=dict(root=physical,complete=not open_steps,eligible_first_steps=possible,open_first_steps=open_steps)
    fully={k.split(":")[0] for k in all_tags if all(summary[k.split(":")[0]+":"+str(e)]["complete"] for e in (0,1))}
    shells={}
    for name in ("distant_two","distant_three"):
        remaining=set(before[name]["unresolved"])-fully
        shells[name]=dict(original_count=before[name]["total"],newly_closed=sorted(fully&set(before[name]["unresolved"])),
                          now_closed=before[name]["total"]-len(remaining),still_open=sorted(remaining))
    earlier=MS/"255-parity-exchange-arms/summary.json"
    longer=MS/"252-shorter-reference-segments/replay-68-192.json"
    distant="e6e522b8cb12744a1906938286731b33b0a5e5acfaff48a9e904ff3a1d14c102"
    if distant not in load(earlier)["references_for_46_overlap"]: raise ValueError("Missing zero- and one-exchange conclusion")
    paths=load(last/"partner-input.json")["shapes"]
    extended=[(k,q) for k,arm in paths.items() for q in extensions(arm)]
    (extension_parent,long_path),=extended
    key=sha256(p.shape(long_path)).hexdigest()
    endpoints=[r for r in load(longer)["endpoints"] if r["id"]==key]
    if (len(paths)!=29 or extension_parent!=before["complete_one_edge_extensions"][0]["source"]
            or len(long_path)!=98 or list(extensions(long_path)) or bank.check_path(long_path,8)!=4753
            or {r["end"] for r in endpoints if r["status"]=="excluded" and r["shortest_excluded"]==192}!={0,1}):
        raise ValueError("Proper-window evidence differs")
    ceiling=46 if shells["distant_two"]["still_open"] else 45 if shells["distant_three"]["still_open"] else 44
    arenas=load(MS/"260-donor-intersections/minimum.json")["rows"]
    for k,r in arenas.items():
        if set(r["parent"][1:])!=pool[summary[k]["root"]][k]: raise ValueError("Normalization mismatch")
    global_path=load(MS.parent/"outputs/snake9_witness.json")["vertex_sequence"]
    if len(global_path)!=192 or bank.check_path(global_path,9)!=18336: raise ValueError("Global witness differs")
    actual=sorted(q.relative_to(HERE).as_posix() for q in (HERE/"proofs").glob("*.gz"))
    if actual!=sorted(files): raise ValueError(("Archive differs",set(actual)-files))
    output=dict(groups=evidence,exhaustive_boolean_assignments=sum(tables.values()),assignments_by_family=tables,
        query_status=freq,distinct_rooted_certificates=len(files),roots=summary,
        roots_complete=sum(r["complete"] for r in summary.values()),formerly_complete=len(all_tags&known),
        open_first_steps=sum(len(r["open_first_steps"]) for r in summary.values()),
        all_first_steps=sum(len(r["eligible_first_steps"]) for r in summary.values()),newly_closed_shapes=sorted(fully),
        shells=shells,distant_reference=distant,smaller_class_overlap_ceiling=ceiling,
        only_proper_extension=dict(parent=extension_parent,shape=key,vertices=long_path,certified_roots=endpoints),
        new_global_witness=best,global_witness_pairs=18336,
        inputs={f.relative_to(MS).as_posix():digest(f) for f in [HERE/"decisions.json",HERE/"family.py",Path(__file__),
            HERE/"cover.py",HERE/"Compatibility263-compile.json",earlier,longer,last/"summary.json",
            last/"partner-input.json",MS/"262-common-forbidden-sites/replay.json",MS/"262-common-forbidden-sites/masks.py"]})
    save(HERE/"summary.json",output)
    print({k:output[k] for k in ("query_status","roots_complete","formerly_complete","all_first_steps","open_first_steps",
                                   "exhaustive_boolean_assignments","newly_closed_shapes")})

if __name__=="__main__": main()
