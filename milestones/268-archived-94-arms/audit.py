"""Rebuild and replay rooted exclusions, checking the archive, maps and first-edge geometry."""
from collections import Counter
from hashlib import sha256
from itertools import combinations, permutations
from pathlib import Path
from tempfile import TemporaryDirectory
from search import HERE, LAST, roots, read, write, base_model, rebuild
from deficit import model as deficit_model


def path_edges(p, dimension):
    assert all(0 <= v < 1 << dimension for v in p) and len(p) == len(set(p))
    for i,j in combinations(range(len(p)),2):
        assert ((p[i]^p[j]).bit_count()==1) == (j==i+1)
    return len(p)-1


def shape(p):
    def steps(path):
        flips=[x^y for x,y in zip(path,path[1:])]
        order=list(dict.fromkeys(flips))
        return bytes(order.index(f) for f in flips)
    return min(steps(p),steps(p[::-1]))


def replay(sites, length, row, tmp, checker):
    common=set.intersection(*sites)
    assert row["prefix"]==[0]
    encoder=deficit_model if row.get("encoding")=="parity-deficit" else base_model
    assert row.get("encoding") in (None,"parity-deficit")
    cnf,chosen=encoder(common,length,[0],row["cycles"],[])
    if len(sites)>1:
        selectors=[]
        for parent in sites:
            lit=cnf.variable()
            selectors.append(lit)
            for v in sorted(parent):
                if v not in common:
                    cnf.clauses.append([-lit,-chosen[v]])
        cnf.clauses.append(selectors)
    f=tmp/"audit.cnf"
    assert cnf.save(f)==row["cnf"] and len(cnf.clauses)==row["clauses"]
    if row["status"]=="excluded":
        proof=HERE/row["proof"]
        assert sha256(proof.read_bytes()).hexdigest()==row["compressed"]
        assert rebuild.masks.p.check_proof(f,proof,checker)==row["replay"]
    elif row["status"]=="witness":
        p=row["path"]
        assert p[0]==0 and path_edges(p,8)==length and any(not s.intersection(p) for s in sites)


def check():
    inputs=roots()
    groups=read(HERE/"groups.json")
    rows={k for group in groups for k in group["ranks"]}
    assert rows==inputs.keys() and len(rows)==sum(len(g["ranks"]) for g in groups)
    examples=set()
    source_shapes={}
    for k,r in inputs.items():
        p=r["parent"]
        assert p[0]==0 and sha256(bytes(p)).hexdigest()==k and path_edges(p,8)==94
        source_shapes.setdefault(shape(p),set()).add(k)
        for name,other in r["partners"].items():
            assert name.startswith("190-") and path_edges(p[::-1]+[256+v for v in other],9)==190
            examples.add(name)
    assert all(len(v)==2 for v in source_shapes.values())
    upgrades={}
    for k,row in read(LAST/"parents.json")["parents"].items():
        if not row["from_191"] or row["retain_edges"]!=94:continue
        starts={name:b for name,b in row["partners"].items() if name.startswith("190-") and len(b)==96}
        if not starts:continue
        records={name:b for name,b in row["partners"].items() if name.startswith("191-") and len(b)==97}
        assert len(starts)==7 and len(records)==5
        parent=row["parent"]
        for name,b in {**starts,**records}.items():
            assert path_edges(parent[::-1]+[256+v for v in b],9)==int(name.split("-")[0])
        upgrades[k]=dict(parent=parent,starting_examples=sorted(starts),record_partners=records)
    write(HERE/"known-upgrades.json",upgrades)
    reused={name for row in upgrades.values() for name in row["starting_examples"]}
    assert not reused & examples and len(reused | examples)==329
    axis_orders=list(permutations(range(8)))
    transfer_file=HERE/"transfers.json"
    transfers=read(transfer_file) if transfer_file.exists() else {}
    if transfers:
        previous=HERE.parent/"267-fixed-arm-extensions"
        previous_arms=read(previous/"cases.json")["roots"]
        previous_bounds=set(read(previous/"summary.json")["coverage"])
        for k,branches in transfers.items():
            fixed=set(inputs[k]["parent"])
            for direction,entry in branches.items():
                first=int(direction)
                assert first.bit_count()==1 and first not in fixed and entry["source"] in previous_bounds
                old=previous_arms[entry["source"]]["parent"]
                assert len(old)==96 and old[0]==0
                perm=axis_orders[entry["rank"]]
                for v in old[1:]:
                    moved=sum(1<<perm[j] for j in range(8) if v&(1<<j)) ^ first
                    assert moved in fixed or (moved!=first and moved.bit_count()==1)
    stats={}
    certified_steps={}
    for query_file in sorted(HERE.glob("queries-*.json")):
        length=int(query_file.stem.split("-")[1])
        group_queries=read(query_file)
        leaf_file=HERE/f"steps-{length}.json"
        leaf_queries=read(leaf_file) if leaf_file.exists() else {}
        shorter={k for n,r in stats.items() if int(n)<length for k in r["covered"]}
        covered=set(shorter)
        found={}
        open_steps={}
        counts=Counter()
        with TemporaryDirectory() as directory:
            tmp=Path(directory)
            checker=rebuild.masks.compilers(tmp)[0]
            for index,group in enumerate(groups):
                parents={}
                for k,rank in group["ranks"].items():
                    perm=axis_orders[rank]
                    p=[sum(1<<perm[j] for j in range(8) if v&(1<<j)) for v in inputs[k]["parent"]]
                    parents[k]=p
                sites=[set(p[1:]) for p in parents.values()]
                assert set.intersection(*sites)==set(group["blocked"])
                whole=group_queries.get(str(index))
                if whole:
                    replay(sites,length,whole,tmp,checker)
                    counts["whole_"+whole["status"]]+=1
                    if whole["status"]=="excluded":
                        covered.update(parents)
                    if whole["status"]=="witness":
                        positive={k:p[::-1]+[256+v for v in whole["path"]] for k,p in parents.items()
                                  if set(p).intersection(whole["path"])=={0}}
                        assert positive==whole["joined"]
                        found.update(positive)
                steps=leaf_queries.get(str(index),{})
                finished=set(certified_steps.get(index,set()))
                for tag,leaf in steps.items():
                    start=int(tag)
                    assert start.bit_count()==1 and 1<=start<256
                    selected={k:p for k,p in parents.items() if start not in p}
                    # An old-coordinate site may belong to the suffix iff it is unused by
                    # the parent, and it is the start or it has distance at least two from zero.
                    family=[{v^start for v in range(256)
                             if v in p or (v!=start and v.bit_count()<2)} for p in selected.values()]
                    replay(family,length-1,leaf,tmp,checker)
                    counts["first_step_"+leaf["status"]]+=1
                    if leaf["status"]=="excluded":
                        finished.add(start)
                    if leaf["status"]=="witness":
                        q=[0]+[v^start for v in leaf["path"]]
                        positive={k:p[::-1]+[256+v for v in q] for k,p in selected.items()
                                  if set(q).intersection(p)=={0}}
                        assert positive==leaf["joined"]
                        found.update(positive)
                for k,p in parents.items():
                    moved=set()
                    perm=axis_orders[group["ranks"][k]]
                    if length==97:
                        moved={1<<perm[int(s).bit_length()-1] for s in transfers.get(k,{})}
                    if all(v in p or v in finished or v in moved for v in (1<<j for j in range(8))):
                        covered.add(k)
                    if k not in covered:
                        open_steps[k]=dict(group=index,first_steps_in_original_coordinates=[
                            1<<d for d in range(8)
                            if (1<<perm[d]) not in set(p)|finished|moved])
                certified_steps[index]=finished
        for q in found.values():
            assert path_edges(q,9)==length+95
        published={k for k,r in inputs.items() if r["partners"]}
        assert not covered & found.keys()
        stats[str(length)] = dict(covered=sorted(covered),excluded_roots=len(covered),
            excluded_already_at_shorter_target=len(shorter),
            excluded_published=len(covered&published),excluded_opposite=len(covered-published),
            excluded_both_ends=sum(s<=covered for s in source_shapes.values()),
            excluded_published_examples=len({e for k in covered for e in inputs[k]["partners"]}),
            unresolved=sorted(rows-covered-found.keys()),witness_roots=sorted(found),counts=counts,
            unresolved_first_steps={k:v for k,v in open_steps.items() if k not in found})
        if found:
            write(HERE/f"attaining-{length+95}.json",found)
            if length+95==191:
                known={shape(r["vertex_sequence"]):i for i,r in enumerate(read(HERE.parent.parent/"work/bank9.json"))}
                stats[str(length)]["archive_matches"]={k:known.get(shape(p)) for k,p in found.items()}
    out=dict(parents_source_sha256=sha256((LAST/"parents.json").read_bytes()).hexdigest(),
             shapes=len(source_shapes),roots=len(rows),archive_examples=len(examples),archive_examples_reusing_record_arms=len(reused),
             published_roots=sum(bool(r["partners"]) for r in inputs.values()),groups=len(groups),targets=stats,
             transferred_first_steps=sum(map(len,transfers.values())))
    certified_starts=[k for k in stats.get("96",{}).get("covered",[]) if inputs[k]["partners"]]
    if certified_starts:
        k=certified_starts[0]
        parent=inputs[k]["parent"]
        name,partner=min(inputs[k]["partners"].items())
        path=parent[::-1]+[v+256 for v in partner]
        assert path_edges(path,9)==190
        write(HERE/"example-190.json",dict(archive=name,root=k,edges=190,crossing_edge=parent[0:1]+[256+partner[0]],
                                         vertices=path,unordered_pairs=len(path)*(len(path)-1)//2))
    write(HERE/"summary.json",out)
    for k,r in stats.items():
        print(k,{t:v for t,v in r.items() if t not in ("covered","unresolved","witness_roots","unresolved_first_steps")},
              "witnesses",len(r["witness_roots"]),"open",len(r["unresolved"]))

if __name__=="__main__":
    check()
