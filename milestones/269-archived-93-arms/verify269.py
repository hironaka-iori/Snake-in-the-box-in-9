"""Independently check transferred coordinates, partner witnesses and certificate coverage."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import permutations
from pathlib import Path
from tempfile import TemporaryDirectory
from opposite import HERE,MS,roots,rebuild,read,write
import importlib.util

spec = importlib.util.spec_from_file_location("round268_replay",MS/"268-archived-94-arms/audit.py")
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)

def next_sites(path,parent):
    return [v for v in range(256) if v not in parent and v not in path
            and (v^path[-1]).bit_count()==1 and all((v^w).bit_count()!=1 for w in path[:-1])]

def review():
    source=roots()
    groups=read(HERE/"groups.json")
    images=list(permutations(range(8)))
    aligned=[]
    registered=[]
    for g in groups:
        group={}
        for k,r in g["ranks"].items():
            p=source[k]["parent"]
            assert p[0]==0 and previous.path_edges(p,8)==93 and sha256(bytes(p)).hexdigest()==k
            axes=images[r]
            group[k]=[sum(1<<axes[i] for i in range(8) if v & 1<<i) for v in p]
        assert sorted(set.intersection(*(set(p[1:]) for p in group.values())))==g["blocked"]
        aligned.append(group)
        registered.extend(group)
    assert len(registered)==len(set(registered))==len(source)==20 and set(registered)==set(source)
    published={k for k,row in source.items() if row["partners"]}
    assert len(published)==10
    evidence={k:dict(lower=190 if k in published else 94, upper=93+1+98) for k in source}
    targets={}
    previous.HERE=HERE  # Certificate paths in the shared replay function are relative to this round.
    with TemporaryDirectory() as d:
        tmp=Path(d)
        checker=rebuild.masks.compilers(tmp)[0]
        for file in sorted(HERE.glob("queries-*.json")):
            length=int(file.stem.split("-")[1])
            excluded=defaultdict(set)
            positive={}
            tally=Counter()
            for label,job in read(file).items():
                i=job["group"]
                keys=job["keys"]
                assert label==",".join(keys) and len(set(keys))==len(keys) and set(keys)<=set(aligned[i])
                group={k:aligned[i][k] for k in keys}
                for address,row in job["rows"].items():
                    prefix=list(map(int,address.split(",")))
                    assert prefix[0]==0 and previous.path_edges(prefix,8)==len(prefix)-1
                    step=prefix[-1]
                    fits={k:p for k,p in group.items() if all(x not in p for x in prefix[1:])}
                    sites=[]
                    for p in fits.values():
                        forbidden={v^step for v in range(256) if v in p[1:] or
                                   (v!=step and any((v^w).bit_count()<=1 for w in prefix[:-1]))}
                        assert 0 not in forbidden
                        sites.append(forbidden)
                    assert sites
                    previous.replay(sites,length+1-len(prefix),row,tmp,checker)
                    tally[row["status"]]+=1
                    if row["status"]=="excluded":
                        for k in fits:excluded[k].add(tuple(prefix))
                    elif row["status"]=="witness":
                        partner=prefix[:-1]+[v^step for v in row["path"]]
                        solutions={k:p[::-1]+[256+v for v in partner] for k,p in group.items()
                                   if set(p).intersection(partner)=={0}}
                        assert solutions==row["joined"] and solutions
                        for k,path in solutions.items():
                            assert previous.path_edges(path,9)==94+length
                            positive[k]=path
            covered=set()
            for group in aligned:
                for k,p in group.items():
                    maximum=max(map(len,excluded[k]),default=0)
                    def closed(path):
                        if tuple(path) in excluded[k]:return True
                        if len(path)>=maximum:return False
                        return all(closed(path+[v]) for v in next_sites(path,set(p)))
                    if closed([0]):covered.add(k)
            assert not covered.intersection(positive)
            for k in covered:evidence[k]["upper"]=min(evidence[k]["upper"],93+length)
            for k in positive:evidence[k]["lower"]=max(evidence[k]["lower"],94+length)
            targets[str(length)]=dict(covered=sorted(covered),witness_roots=sorted(positive),counts=tally)
            if positive:
                write(HERE/f"attaining-{94+length}.json",positive)
    cpath=HERE/"partner-census.json"
    if cpath.exists():
        census=read(cpath)
        for k,levels in census["extensions"].items():
            attained=[int(n) for n,count in levels.items() if count]
            if attained:evidence[k]["lower"]=max(evidence[k]["lower"],94+max(attained))
            if k in census["closed_roots"]:
                cap=94+(max(attained) if attained else 95)
                evidence[k]["upper"]=min(evidence[k]["upper"],cap)
    placements=read(HERE/"placements.json")["roots"]
    assert set(placements)==set(source)
    for k,record in placements.items():
        parent=source[k]["parent"]
        w=record["best"]
        assert record["parent"]==w["A"]==parent
        assert parent[::-1]+[256+v for v in w["B"]]==w["joined"]
        assert previous.path_edges(w["joined"],9)==w["edges"]
        evidence[k]["lower"]=max(evidence[k]["lower"],w["edges"])
    for k,r in evidence.items():
        assert r["lower"]<=r["upper"]
        if k not in published and r["lower"]==94:
            # Any projected neighbour of zero outside the parent provides a one-edge arm.
            b=next(v for v in next_sites([0],set(source[k]["parent"])))
            assert previous.path_edges(source[k]["parent"][::-1]+[256,256+b],9)==95
            r["lower"]=95
    pairs={}
    for k,row in source.items():
        sh=sha256(previous.shape(row["parent"])).hexdigest()
        pairs.setdefault(sh,[]).append(k)
    assert len(pairs)==10 and all(len(s)==2 for s in pairs.values())
    short=dict(targets=targets,roots=evidence,shapes=pairs,excluded_192=sum(v["upper"]<192 for v in evidence.values()),
               excluded_published_192=sum(evidence[k]["upper"]<192 for k in published),
               published_exact=Counter(v["upper"] for k,v in evidence.items() if k in published and v["upper"]==v["lower"]),
               archive_parent_source=sha256((MS/"266-rebuilding-one-arm/parents.json").read_bytes()).hexdigest())
    write(HERE/"summary.json",short)
    print("Targets",[(n,len(t["covered"]),len(t["witness_roots"]),dict(t["counts"])) for n,t in targets.items()],
          "published exact",short["published_exact"],"excluded at 192",short["excluded_192"],flush=True)

if __name__=="__main__":review()
