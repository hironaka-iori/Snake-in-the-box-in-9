"""Recover every reference that generates each long shape and exact minimum seed covers."""
from collections import Counter
from functools import lru_cache
from pathlib import Path
from hashlib import sha256
import json
from census import HERE, BASE, LAST, read, references, shape_id, audit


def selected_cover(masks, universe):
    by_column={i:tuple(j for j,m in enumerate(masks) if m>>i & 1)
               for i in range(universe.bit_length())}
    @lru_cache(None)
    def cover(left):
        if not left:return ((),1)
        pivot=min((i for i in by_column if left>>i&1),key=lambda i:len(by_column[i]))
        options=[]
        for j in by_column[pivot]:
            used,_=cover(left&~masks[j])
            options.append(tuple(sorted((j,*used))))
        best=min(options,key=lambda s:(len(s),s))
        return best, len(options)
    return cover(universe)[0],cover.cache_info().currsize


def main():
    sources=references()
    paths={shape_id(p):p for p in sources.values()}
    files=[BASE/"250-corner-partners"/"cores-84.json",LAST/"census-72.json",HERE/"census-68.json"]
    for f in files:
        for r in read(f)["new_shapes"]:paths[r["id"]]=r["path"]
    census=read(files[-1])
    ids=sorted(paths)
    if ids!=census["all_ids"]:raise ValueError("Shape coverage differs")
    rows={}
    all_origins={i:[] for i in ids}
    for label,source in sources.items():
        per=set(audit.key(source[t:t+69]) for t in range(len(source)-68))
        rows[label]=set()
        for key,path in paths.items():
            if any(audit.key(path[t:t+69]) in per for t in range(len(path)-68)):
                rows[label].add(key)
                all_origins[key].append(label)
    labels=list(rows)
    masks=[sum(1<<i for i,key in enumerate(ids) if key in rows[label]) for label in labels]
    universe=(1<<len(ids))-1
    chosen,states=selected_cover(masks,universe)
    if set.union(*(rows[labels[j]] for j in chosen))!=set(ids):raise ValueError("Missing class")
    # Independent lower bound by enumerating all subsets of representatives of
    # distinct, inclusion-maximal row masks. Replacing a dominated row is safe.
    from itertools import combinations
    maximal=sorted(m for m in set(masks) if not any(m!=h and m&~h==0 for h in masks))
    def reaches(combo):
        m=0
        for item in combo:m|=item
        return m==universe
    smaller=sum(reaches(c) for c in combinations(maximal,len(chosen)-1))
    if smaller!=0:raise ValueError("Smaller cover exists")
    prev=set(read(files[1])["inherited_ids"])|{r["id"] for r in read(files[1])["new_shapes"]}
    per_ref=[dict(id=l,edges=len(sources[l])-1,classes=len(rows[l]),new_classes=len(rows[l]-prev),
                  new_by_length=Counter(len(paths[i])-1 for i in rows[l]-prev),
                  unique_to_reference=[i for i in sorted(rows[l]) if len(all_origins[i])==1])
             for l in labels]
    out=dict(inputs={f.name:audit.digest(f) for f in [*files,Path(__file__),audit.INVENTORY,audit.GEOMETRY]},
        incidence=all_origins,per_reference=per_ref,minimum_reference_cover=[labels[j] for j in chosen],
        set_cover_states=states,maximal_distinct_rows=len(maximal),covering_subsets_one_smaller=smaller,
        new_by_maximum_common_segment=Counter(r["longest_reference_segment"] for r in census["new_shapes"]))
    (HERE/"origins.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("Minimum seed cover",out["minimum_reference_cover"],"new by largest segment",out["new_by_maximum_common_segment"])
    for r in per_ref:
        if r["edges"]==98 or r["new_classes"]>=10:print(r["id"],r["edges"],r["classes"],r["new_classes"])


if __name__=="__main__":main()
