"""Compare original-coordinate witnesses with archived paths and enumerate all immediate tip extensions."""
from collections import Counter
from rebuild_saved import MS,HERE,face,read,save,MAIN

def main():
    hunt=face.dependencies(MS)
    from exchange import input_paths
    built=read(HERE/"constructions.json")
    repairs=read(HERE/"whole-path-repairs.json") if (HERE/"whole-path-repairs.json").exists() else {}
    shapes={}
    def include(seq,k,source):
        edges=hunt.original_audit.path_edges(seq,9)
        if edges<189:return
        sig=hunt.original_audit.shape(seq).hex()
        if sig not in shapes:
            tips=[]
            for p in (seq,seq[::-1]):
                v=p[-1]
                tips.append([z for i in range(9) if (z:=v^(1<<i)) not in p and
                             all((u^z).bit_count()!=1 for u in p[:-1])])
            uses=[sum((u^v)==1<<a for u,v in zip(seq,seq[1:])) for a in range(9)]
            shapes[sig]=dict(edges=edges,ordered=seq,unordered_vertex_pairs=len(seq)*(len(seq)-1)//2,
                             coordinate_uses=uses,once_crossed=[i for i,n in enumerate(uses) if n==1],
                             reverse_then_forward_tip_options=tips,roots=[],archive=[])
        shapes[sig]["roots"].append(dict(k=k,source=source))
    for k,w in built.items():
        include(w["original_joined"],k,"fixed")
    for k,r in repairs.items():
        for item in r["shapes"].values():include(item["joined"],k,"whole-path-repair")
    for f in sorted(HERE.glob("growth-from-*.json")):
        for v in read(f)["children"].values():
            for k in v["first_roots"]:include(v["joined"],k,f.stem)
    sizes={r["edges"] for r in shapes.values()};counts=Counter();archive=Counter()
    for name,seq in input_paths():
        archive[len(seq)-1]+=1
        for n in sizes:
            for i in range(len(seq)-n):
                counts[n]+=1
                sig=hunt.original_audit.shape(seq[i:i+n+1]).hex()
                if sig in shapes:shapes[sig]["archive"].append(dict(archive=name,first=i))
    save(HERE/"classified.json",dict(archive=archive,verified_windows=counts,shapes=shapes))
    best=max(shapes.values(),key=lambda s:(s["edges"],not s["archive"],any(x["k"]==MAIN for x in s["roots"])))
    save(HERE/"longest.json",best)
    print("Classes by length",Counter(r["edges"] for r in shapes.values()),"absent from bank windows",
          Counter(r["edges"] for r in shapes.values() if not r["archive"]),flush=True)
if __name__=="__main__":main()
