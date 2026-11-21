"""Transport, repair and regrow partners at five selected roots of the 68-edge closure."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from random import Random
import json
import sys

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
PREV=BASE/"252-shorter-reference-segments"
sys.path.insert(0,str(PREV))
import construct as search


def full_maps(word, allowed):
    """Track up to four parent collisions on a complete proposed partner."""
    masks=[search.bank.ALL_MAPS,0,0,0,0]
    length=rank=0
    for i,v in enumerate(word[1:],1):
        usable=allowed[v]
        masks=[masks[0]&usable]+[(masks[j]&usable)|(masks[j-1]&~usable) for j in range(1,5)]
        if masks[0]:
            length,rank=i,(masks[0]&-masks[0]).bit_length()-1
        if not any(masks):
            break
    return length,rank,masks


def repair_clusters(path, forbidden, rng):
    path=path.copy()
    while True:
        hits=[(i,x) for i,x in enumerate(path) if forbidden&(1<<x)]
        if not hits: return path
        if hits[-1][0]>=len(path)-2:
            path=path[:hits[-1][0]]
            continue
        # While fixing the earliest group, the other collided vertices remain
        # occupied by their fixed positions. They cannot be used by a new bridge.
        split=1
        while split<len(hits) and hits[split][0]-hits[split-1][0]<=6:
            split+=1
        other=sum(1<<x for _,x in hits[split:])
        amended=search.repair(path,forbidden & ~other,rng,420)
        if not amended:
            return path[:hits[0][0]]
        path=amended


def amplify(parent,seed,rng):
    """Regrow various suffixes and try interior detours around one disallowed site."""
    outside=search.path_mask(parent[1:])
    best=seed.copy()
    active=best.copy()
    for phase in range(8):
        for _ in range(64):
            i=rng.randrange(1,len(active)-1)
            replacement=search.repair(active,outside | (1<<active[i]),rng,1100)
            if replacement and (len(replacement)>len(active) or
                                (len(replacement)>=len(active)-2 and rng.random()<0.12)):
                active=replacement
                if len(active)>len(best):
                    search.check_join(parent,active)
                    best=active.copy()
        tail=search.tail_search(parent,active,rng)
        if len(tail)>len(best):
            search.check_join(parent,tail)
            best=tail.copy()
        active=best.copy() if phase%3==0 else tail
    return best


def main():
    old=PREV/"construct-68.json"
    archive=BASE/"248-rooted-arm-capacity"/"attainers.json"
    prior=BASE/"251-eighty-edge-segments"/"regrowth-witnesses.json"
    closure=HERE/"closure.json"
    placements=HERE/"placements.json"
    files=[old,archive,prior,closure,placements,Path(search.__file__),Path(search.bank.__file__),Path(__file__)]
    pins={p.relative_to(BASE).as_posix():sha256(p.read_bytes()).hexdigest() for p in files}
    old_records=search.read(old)["cases"]
    if len(old_records)!=70: raise ValueError("Incomplete Round 252 partner inventory")
    named=[(str(old.relative_to(BASE)),r["id"]+":"+str(r["end"]),r["partner"]) for r in old_records]
    named.extend((str(prior.relative_to(BASE)),r["id"]+":"+str(r["end"]),r["partner"])
                 for r in search.read(prior)["cases"])
    for r in search.read(archive)["records"]:
        for i,p in enumerate(r["paths"]):
            named.append((str(archive.relative_to(BASE)),str(r["class_id"])+":"+str(i),p["path"]))
    library={}
    for source,label,p in named:
        search.bank.check_path(p,8)
        for end,q in enumerate((p,p[::-1])):
            library.setdefault(search.relabel(q),dict(source=source,label=label,end=end))
    paths=search.read(closure)["paths"]
    census=search.read(placements)
    if not census["summary"]["complete"]: raise ValueError("Placement census incomplete")
    distant=[k for k in sorted(paths) if k.startswith(("6f8ef24c","bac52b55"))]
    if len(distant)!=2: raise ValueError("Ambiguous distant shapes")
    candidates=[(k,e) for k in distant for e in range(2)]
    extra=min((c for c in census["cases"] if c["id"] not in distant),
              key=lambda c:(-c["banks"]["closure"]["partner_edges"],c["id"],c["end"]))
    candidates.append((extra["id"],extra["end"]))
    images=list(search.bank.permutation_images())
    results=[]
    for key,end in candidates:
        rng=Random(int(key[:16],16)*2+end)
        order=paths[key] if end==0 else paths[key][::-1]
        parent=[x^order[0] for x in order]
        old_case=next(c for c in census["cases"] if (c["id"],c["end"])==(key,end))
        baseline=max(old_case["banks"].values(),key=lambda b:b["partner_edges"])["partner"]
        allowed=search.bank.allowed_maps(parent,images)
        forbidden=search.path_mask(parent[1:])
        longest=[0]
        prefix_origin=None
        near=[]
        exact_counts=Counter()
        for word,origin in library.items():
            plen,rank,levels=full_maps(word,allowed)
            if plen>=len(longest):
                longest=list(word[:plen+1].translate(images[rank]))
                prefix_origin=dict(**origin,permutation_rank=rank)
            for count,maps in enumerate(levels):
                exact_counts[count]+=maps.bit_count()
                if not count: continue
                for _ in range(8):
                    if not maps: break
                    bit=maps&-maps; maps-=bit
                    rank=bit.bit_length()-1
                    q=list(word.translate(images[rank]))
                    hits=[i for i,x in enumerate(q) if forbidden&(1<<x)]
                    if len(hits)!=count: raise ValueError("Collision count mismatch")
                    near.append((-len(q),count,hits[-1]-hits[0],q))
        seed=max((baseline,longest),key=len)
        distinct=set()
        for _,__,___,q in sorted(near):
            marker=bytes(q)
            if marker in distinct: continue
            distinct.add(marker)
            revised=repair_clusters(q,forbidden,rng)
            if len(revised)>len(seed):
                search.check_join(parent,revised)
                seed=revised
            if len(distinct)>=120: break
        improved=amplify(parent,seed,rng)
        result=search.check_join(parent,improved)
        results.append(dict(id=key,end=end,root=order[0],parent_edges=len(parent)-1,bank_lower=len(baseline)-1,
                            transported_prefix_edges=len(longest)-1,prefix_origin=prefix_origin,
                            near_full_placement_counts=exact_counts,repair_candidates_tried=len(distinct),
                            after_initial_repair=len(seed)-1,**result))
        print(key[:9],end,"bank",len(baseline)-1,"prefix",len(longest)-1,"repaired seed",len(seed)-1,
              "unrestricted",len(improved)-1,"join",result["joined_edges"],flush=True)
    data=dict(pins=pins,original_sources=Counter(s for s,_,_ in named),directed_seed_shapes=len(library),
              axis_permutations_per_seed=search.bank.PERMUTATIONS,cases=results)
    (HERE/"remote-arms.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")


if __name__=="__main__":main()
