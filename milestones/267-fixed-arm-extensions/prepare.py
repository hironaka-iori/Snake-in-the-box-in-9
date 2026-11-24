"""Index fixed parents and their crossing endpoints for the complete opposite-arm search."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
LAST=MS/"266-rebuilding-one-arm"
sys.path.insert(0,str(LAST))
from catalogue import label,identifier,read,write
from align import pack,bank

def shape_id(p):
    def steps(path):
        edges=[v^w for v,w in zip(path,path[1:])]
        lut=list(dict.fromkeys(edges))
        return bytes(lut.index(x) for x in edges)
    return sha256(min(steps(p),steps(p[::-1]))).hexdigest()

def main():
    old=read(LAST/"parents.json")["parents"]
    window=read(LAST/"windows.json")
    roots={}
    for p in window["paths"].values():
        if len(p)<96:
            continue
        for q in (p,p[::-1]):
            seq=label(q)[0]
            k=identifier(seq)
            roots.setdefault(k,dict(parent=seq,window=True,archive=False,partners={}))
    for k,row in old.items():
        if row["retain_edges"]==95:
            r=roots.setdefault(k,dict(parent=row["parent"],window=False))
            assert r["parent"]==row["parent"]
            r.update(archive=True,partners=row["partners"])
    oldcaps=read(LAST/"summary.json")
    exact=read(MS/"252-shorter-reference-segments/replay-68-192.json")
    assert exact["all_excluded"]
    excluded=set(read(MS/"252-shorter-reference-segments/census-68.json")["all_ids"])
    reached={}
    for k,r in roots.items():
        p=r["parent"]
        # A 95-edge parent with a published 94-edge prefix would require
        # a 96-edge partner from its exact census. Every survivor must avoid the new tip.
        pre=identifier(label(p[:95])[0])
        if len(p)==96 and pre in old and old[pre]["from_191"]:
            candidates=[b for b in old[pre]["partners"].values() if len(b)==97]
            assert all(p[-1] in b for b in candidates) and pre in set(oldcaps["other_end_bounds"])|set(oldcaps["archived_attainers"])
            reached[k]=dict(reason="94-edge census",source=pre,blocked_partners=len(candidates))
        if len(p)==97 and shape_id(p) in excluded:
            reached[k]=dict(reason="68-edge interval",source=shape_id(p))
    images=list(bank.permutation_images())
    groups={}
    # Include inherited roots in these families as well. A family contradiction
    # at partner length 95 can be stronger than an earlier 96-edge exclusion.
    for n in (95,96):
        part={k:r["parent"] for k,r in roots.items() if len(r["parent"])==n+1}
        found=pack(part,images,n-5)
        for i,g in enumerate(found):
            groups[f"{n}-{i}"]=g
    write(HERE/"cases.json",dict(roots=roots,inherited=reached,groups=groups))
    print("Fixed endpoints",Counter(len(r["parent"])-1 for r in roots.values()),"of which window",sum(r["window"] for r in roots.values()),"inherited",len(reached))
    print("Groups",[(k,len(v["ranks"]),len(v["blocked"])) for k,v in groups.items()])

if __name__=="__main__":main()
