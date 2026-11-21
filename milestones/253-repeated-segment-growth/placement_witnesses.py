"""Reconstruct the saved 696 extremal bank witnesses directly from their source records."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parent


def read(path):
    return json.loads(path.read_bytes())


def check(path,dimension):
    if len(set(path))!=len(path) or any(v<0 or v>=2**dimension for v in path):
        raise ValueError("Invalid vertices")
    for j,v in enumerate(path):
        for i in range(j):
            if ((path[i]^v).bit_count()==1)!=(i+1==j):
                raise ValueError("Incorrect adjacency")
    return len(path)*(len(path)-1)//2


def main():
    file=HERE/"placements.json"
    data=read(file)
    for name,pin in data["pins"].items():
        if sha256((BASE/name).read_bytes()).hexdigest()!=pin:
            raise ValueError("Source hash mismatch")
    closure=read(HERE/"closure.json")
    inherited=read(BASE/"252-shorter-reference-segments"/"census-68.json")
    shapes=set(closure["paths"])-set(inherited["all_ids"])
    cardinalities={name:len(g["source_shape_labels"]) for name,g in data["banks"].items()}
    cached={}
    cases=set()
    histograms={name:Counter() for name in cardinalities}
    maxima={}
    pairs=Counter()
    for case in data["cases"]:
        key,end=case["id"],case["end"]
        if (key,end) in cases or key not in shapes or end not in (0,1):
            raise ValueError("Incorrect root")
        cases.add((key,end))
        vertices=closure["paths"][key]
        order=vertices if end==0 else vertices[::-1]
        parent=[v^order[0] for v in order]
        if case["root"]!=order[0] or case["parent_edges"]!=len(parent)-1 or case["banks"].keys()!=cardinalities.keys():
            raise ValueError("Root label or banks differ")
        for name,r in case["banks"].items():
            source,*location=data["banks"][name]["source_shape_labels"][r["donor"]]
            path=(HERE if source=="closure.json" else BASE)/source
            if path not in cached: cached[path]=read(path)
            target=cached[path]
            for component in location:target=target[component]
            axes=r["axis_images"]
            if sorted(axes)!=list(range(8)) or r["direction"] not in (1,-1):
                raise ValueError("Invalid placement")
            indices=[r["start"]+r["direction"]*i for i in range(r["partner_edges"]+1)]
            if any(not 0<=j<len(target) for j in indices):
                raise ValueError("Source segment exceeds donor")
            anchor=target[indices[0]]
            partner=[sum(1<<axes[a] for a in range(8) if (target[i]^anchor)&(1<<a)) for i in indices]
            joined=parent[::-1]+[v+256 for v in partner]
            if r["partner"]!=partner or len(joined)-1!=r["joined_edges"] or set(parent)&set(partner)!={0}:
                raise ValueError("Incorrect joining path")
            observed={"parent":check(parent,8),"partner":check(partner,8),"joined":check(joined,9)}
            if observed!=r["all_pairs"]:
                raise ValueError("Pair count mismatch")
            pairs.update(observed)
            exclusion=r["next_length_exclusion"]
            if (exclusion["edges"]!=r["partner_edges"]+1 or exclusion["axis_maps"]!=40320
                    or exclusion["compatible_placements"]!=0):
                raise ValueError("Missing next-length placement receipt")
            histograms[name][r["joined_edges"]]+=1
            if name not in maxima or r["joined_edges"]>maxima[name]["joined_edges"]:
                maxima[name]=dict(id=key,end=end,root=case["root"],parent_edges=len(parent)-1,
                                  partner_edges=len(partner)-1,joined_edges=len(joined)-1,
                                  partner_source=[source,*location],joined=joined)
    if cases!={(k,e) for k in shapes for e in (0,1)} or not data["summary"]["complete"]:
        raise ValueError("Missing roots")
    for name,counts in histograms.items():
        saved=data["summary"]["by_bank"][name]
        if {int(k):v for k,v in saved["join_histogram"].items()}!=counts or saved["maximum_join"]!=max(counts):
            raise ValueError("Summary differs from records")
    result=dict(verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                placements_sha256=sha256(file.read_bytes()).hexdigest(),roots=len(cases),
                witnesses=sum(sum(v.values()) for v in histograms.values()),pair_comparisons=dict(pairs),
                donor_shapes=cardinalities,maxima=maxima,join_histograms=histograms)
    (HERE/"placement-witnesses.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(len(cases),"roots.",{name:r["joined_edges"] for name,r in maxima.items()})


if __name__=="__main__":main()
