"""Replay certificates and reconstruct the fixed-arm census and two-ended extension catalogue."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import json

from rebuild import HERE, MS, load, save, masks, geometry, model


def word(path):
    steps=[x^y for x,y in zip(path,path[1:])]
    def oriented(seq):
        lookup={}
        return bytes(lookup.setdefault(v,len(lookup)) for v in seq)
    return min(oriented(steps),oriented(steps[::-1]))


def extend_one_end(path):
    sites=set(path)
    return [path+[v] for v in range(256) if v not in sites and (v^path[-1]).bit_count()==1
            and all((v^w).bit_count()!=1 for w in path[:-1])]


def audit_windows(catalogue,roots):
    outputs=set()
    def grow_right(p):
        outputs.add(word(p))
        if len(p)<99:
            for q in extend_one_end(p):
                grow_right(q)
    def grow_left(p):
        grow_right(p[::-1])
        if len(p)<99:
            for q in extend_one_end(p):
                grow_left(q)
    for r in roots:
        grow_left(r["parent"])
    assert outputs=={word(p) for p in catalogue["paths"].values()}
    return Counter(map(len,outputs))


def main():
    parents=load(HERE/"parents.json")["parents"]
    active={k:r for k,r in parents.items() if r["from_191"]}
    bank=load(MS.parent/"work/bank9.json")
    known={word(r["vertex_sequence"]):i for i,r in enumerate(bank)}
    assert len(active)==10
    placed=load(HERE/"constructed.json")["roots"]
    certs={}
    with TemporaryDirectory() as d:
        tmp=Path(d)
        checker=masks.compilers(tmp)[0]
        for file in sorted(HERE.glob("partner-*.json")):
            target=int(file.name.split("-")[1].split(".")[0])
            ledger=load(file)
            assert ledger["parents_sha256"]==masks.digest(HERE/"parents.json")
            for k,rows in ledger["roots"].items():
                case=active[k]
                parent=case["parent"]
                blocked=set(parent[1:])
                n=target-len(parent)
                old=sorted(set(tuple(v) for v in case["partners"].values() if len(v)==n+1)) if "census" in file.stem else []
                for row in rows.values():
                    cnf,_=model(blocked,n,row["prefix"],row["cycles"],old)
                    f=tmp/"replay.cnf"
                    assert cnf.save(f)==row["cnf"]
                    if row["status"]=="excluded":
                        fp=HERE/row["proof"]
                        assert masks.digest(fp)==row["compressed"]
                        actual=masks.p.check_proof(f,fp,checker)
                        assert actual==row["replay"]
                    if row["status"]=="witness":
                        geom=parent[::-1]+[256+v for v in row["path"]]
                        assert len(geom)-1==target and geom==row["joined"]
                        geometry.verify(geom,9)
            certs[file.name]=dict(hash=masks.digest(file),outcomes=Counter(r["status"] for rows in ledger["roots"].values() for r in rows.values()))
    extremal={}
    reverse={}
    for k,r in active.items():
        parent=r["parent"]
        assert load(HERE/"partner-192.json")["roots"][k]["0"]["status"]=="excluded"
        assert load(HERE/"partner-191-census.json")["roots"][k]["0"]["status"]=="excluded"
        case=[]
        for b in r["partners"].values():
            if len(b)==97:
                path=parent[::-1]+[256+v for v in b]
                geometry.verify(path,9)
                case.append(known[word(path)])
                assert not any(set(q).intersection(b)=={0} for q in extend_one_end(parent))
        assert len(case) in (0,5)
        if case:
            extremal[k]=sorted(case)
        else:
            lo=placed[k]["best"]["edges"]
            hi=190
            for file in HERE.glob("partner-*.json"):
                row=load(file)["roots"].get(k,{}).get("0",{})
                if "census" in file.stem:
                    continue
                n=int(file.stem.split("-")[1])
                if row.get("status")=="witness":
                    lo=max(lo,n)
                if row.get("status")=="excluded":
                    hi=min(hi,n-1)
            reverse[k]=[lo,hi]
            assert lo<=hi
        geometry.verify(placed[k]["best"]["joined"],9)
    ids=[i for ns in extremal.values() for i in ns]
    assert len(set(ids))==len(ids)==25
    windows=audit_windows(load(HERE/"windows.json"),[active[k] for k in extremal])
    results=dict(archived_attainers=extremal,other_end_bounds=reverse,certificates=certs,
                 windows_by_edges=windows,source_sha256=masks.digest(Path(__file__)),
                 global_witness_length=len(load(MS.parent/"outputs/snake9_witness.json")["vertex_sequence"])-1)
    save(HERE/"summary.json",results)
    print("Attainers:",len(ids),"windows:",windows,"opposite ends:",reverse)

if __name__=="__main__":
    main()
