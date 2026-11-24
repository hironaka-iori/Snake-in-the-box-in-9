"""Search all 95-edge partners of at least one fixed, labelled parent in a group."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

from prepare import HERE, MS, LAST, read, write, bank
from rebuild import masks, geometry

def grouped_inputs(data,group,images):
    aligned={k:list(bytes(data["roots"][k]["parent"]).translate(images[rank])) for k,rank in group["ranks"].items()}
    common=set.intersection(*(set(p[1:]) for p in aligned.values()))
    assert sorted(common)==group["blocked"]
    return aligned,common,[sorted(set(p[1:])-common) for p in aligned.values()]


def formula(seen):
    def build(blocked,cycles,extras,prefix):
        cnf,chosen=masks.formula(blocked,cycles,extras,prefix)
        for w in seen:
            path=w["path"]
            assert len(path)==96 and path[0]==0 and not blocked.intersection(path)
            cnf.clauses.append([-chosen[v] for v in sorted(path)])
        return cnf,chosen
    return build


def classify(path,aligned):
    result={}
    for k,p in aligned.items():
        if set(path)&set(p)!={0}:
            continue
        seq=p[::-1]+[256+v for v in path]
        pairs=bank.check_path(seq,9)
        add=[v for v in geometry.NEIGHBOURS[path[-1]] if v not in p and v not in path and
             all((v^w).bit_count()!=1 for w in path[:-1])]
        result[k]=dict(edges=len(seq)-1,pairs=pairs,extensions=add)
        for v in add:
            bank.check_path(seq+[v+256],9)
    assert result
    return result


def main():
    ap=ArgumentParser()
    ap.add_argument("--seconds",type=float,default=4)
    ap.add_argument("--window",action="store_true")
    ap.add_argument("--named",nargs="+")
    ap.add_argument("--depth",type=int,default=0)
    ap.add_argument("--limit",type=int,default=4)
    opt=ap.parse_args()
    data=read(HERE/"cases.json")
    dest=HERE/"families.json"
    catalogue=read(dest) if dest.exists() else {}
    images=list(bank.permutation_images())
    with TemporaryDirectory() as d:
        work=Path(d)
        tools=masks.compilers(work)
        for name,g in data["groups"].items():
            pending_window=any(data["roots"][k]["window"] and k not in data["inherited"] for k in g["ranks"])
            if (opt.window and not pending_window) or (opt.named and name not in opt.named):
                continue
            aligned,core,extras=grouped_inputs(data,g,images)
            entry=catalogue.setdefault(name,dict(queries={},witnesses=[]))
            if entry["queries"].get("0",{}).get("status")=="excluded":
                continue
            prefixes=[[0]] if not opt.depth else [[0,v] for v in geometry.NEIGHBOURS[0] if v not in core and any(v not in p for p in aligned.values())]
            for prefix in prefixes:
                label=",".join(map(str,prefix))
                prev=entry["queries"].get(label,{})
                if prev.get("status")=="excluded":
                    continue
                for _ in range(opt.limit):
                    count=len(entry["witnesses"])
                    ans=masks.query(HERE,work,tools,core,opt.seconds,extras,prefix,prev if prev else None,builder=formula(entry["witnesses"]))
                    ans["prior_witnesses"]=count
                    entry["queries"][label]=ans
                    if ans["status"]=="witness":
                        found=classify(ans["path"],aligned)
                        entry["witnesses"].append(dict(path=ans["path"],compatible=found,prefix=prefix))
                        for k,r in found.items():
                            if r["edges"]>=192 or r["extensions"]:
                                joined=aligned[k][::-1]+[v+256 for v in ans["path"]]
                                if r["edges"]<192:
                                    joined.append(256+r["extensions"][0])
                                write(HERE/"candidate-192.json",dict(parent=k,joined=joined,pairs=bank.check_path(joined,9)))
                                write(dest,catalogue)
                                return
                    write(dest,catalogue)
                    print(name,len(aligned),prefix,ans["status"],len(entry["witnesses"]),flush=True)
                    if ans["status"]!="witness":
                        break
                    prev=ans

if __name__=="__main__":
    main()
