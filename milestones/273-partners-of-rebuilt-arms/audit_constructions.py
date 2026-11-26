"""Recount the closest projected donors and compare verified Q9 constructions with the archives."""
from collections import Counter,defaultdict
from hashlib import sha256
from itertools import combinations
from importlib.util import spec_from_file_location,module_from_spec
from search_partners import hunt,HERE,MS,R271,read,write
spec=spec_from_file_location("rebuilt_placement",HERE/"construct.py")
placement=module_from_spec(spec);spec.loader.exec_module(placement)
R270,R272,bank=placement.R270,placement.R272,placement.bank
source_shapes,donor_words=placement.source_shapes,placement.donor_words
rename,physical,word=placement.rename,placement.physical,placement.word
from exchange import input_paths

def recount():
    data=read(HERE/"opposite-constructions.json")
    roots=data["roots"];fresh,old=source_shapes();donors,shortlist=donor_words(fresh)
    assert sha256((R272/"q8-arms.json").read_bytes()).hexdigest()==data["source_sha256"]
    assert len(set(fresh)&old)==data["earlier_whole_controls"]
    assert len(donors)==data["donor_shapes"] and len(shortlist)==data["near_donors"]
    maps=list(bank.permutation_images())
    totals=Counter();per_root={}
    lengths={192-len(r["parent"]) for r in roots.values()}
    words={n:{rename(s[:n]) for code in shortlist for s in (code,code[::-1]) if len(s)>=n-4} for n in lengths}
    for k,r in roots.items():
        p=r["parent"];near=r["repair_start"];n=192-len(p)
        assert sha256(bytes(p)).hexdigest()==k and word(p).hex()==r["shape"]
        masks=bank.allowed_maps(p,maps);gap=near["needed_new_sites"]
        for w in words[n]:
            cap=gap-(n-len(w))-1
            if cap<0:continue
            alive=[bank.ALL_MAPS]*(cap+1)
            for u in reversed(physical(w)[1:]):
                good=masks[u];bad=bank.ALL_MAPS^good
                alive=[(good&v)|(bad&alive[j-1] if j else 0) for j,v in enumerate(alive)]
                if not alive[-1]:break
            assert not alive[-1],(k,w.hex(),gap)
        w=bytes.fromhex(near["word"]);donor=list(physical(w).translate(maps[near["rank"]]))
        assert w in words[n] and donor==near["donor"] and len(donor[1:])<=n
        conflicts=set(donor[1:])&set(p)
        assert sorted(conflicts)==near["intersections"] and n-len(w)+len(conflicts)==gap
        q=r["best"]["joined"]
        assert q==p[::-1]+[256+v for v in r["best"]["B"]]
        assert hunt.original_audit.path_edges(q,9)==r["best"]["edges"]
        totals[gap]+=1
        per_root[k]=dict(minimum_new_sites=gap,shortlist_directed_patterns=len(words[n]))
    out=dict(verified_roots=len(roots),gaps=totals,roots=per_root,
             inverse_threshold_recurrence=True,shape_source_sha256=data["source_sha256"])
    write(HERE/"placement-replay.json",out)
    print("Verified minimum replacements",totals,flush=True)

def catalogue():
    data=read(HERE/"summary.json");known=read(HERE/"additional-witnesses.json")
    roots=read(HERE/"opposite-constructions.json")["roots"]
    union=dict(roots)
    for k,r in read(R270/"opposite-constructions.json")["roots"].items():
        assert k not in union;union[k]=r
    earlier=read(R271/"summary.json")["roots"]
    bounds={**data["roots"],**earlier}
    intervals=hunt.interval_bounds(union,bounds)
    newshapes={r["shape"] for r in roots.values()}
    own={k:r for k,r in intervals["intervals"].items() if k in newshapes}
    write(HERE/"containing-arms.json",dict(complete_families=sum(r["ceiling"] is not None for r in own.values()),
          excluded_192=sum(r["ceiling"] is not None and r["ceiling"]<192 for r in own.values()),
          outside=intervals["outside_shapes"],intervals=own))
    paths={}
    for k,r in roots.items():
        p=r["best"]["joined"]
        for cand in (p,*known.get(k,{}).values()):
            edges=len(cand)-1
            if edges<min(189,data["maximum_constructed"]):continue
            assert hunt.original_audit.path_edges(cand,9)==edges
            code=hunt.original_audit.shape(cand).hex()
            tips=[]
            for ordered in (cand,cand[::-1]):
                tip=ordered[-1]
                tips.append([u for a in range(9) if (u:=tip^(1<<a)) not in ordered and
                             not any((v^u).bit_count()==1 for v in ordered[:-1])])
            if code not in paths:paths[code]=dict(root=k,edges=edges,joined=cand,tip_extensions=tips,matches=[])
    sizes={r["edges"] for r in paths.values()};archive=Counter();intervals_count=0
    for label,seq in input_paths():
        archive[len(seq)-1]+=1
        for n in sizes:
            for j in range(len(seq)-n):
                sig=hunt.original_audit.shape(seq[j:j+n+1]).hex()
                intervals_count+=1
                if sig in paths:paths[sig]["matches"].append([label,j])
    write(HERE/"long-constructions.json",dict(archive=archive,intervals_checked=intervals_count,paths=paths))
    best=read(HERE/"best-join.json");first=best["root"];first_shape=roots[first]["shape"]
    def q9_path(k):
        n=data["roots"][k]["minimum"]
        return known.get(k,{}).get(str(n),roots[k]["best"]["joined"])
    eligible=[k for k in roots if roots[k]["shape"]!=first_shape]
    if eligible:
        extensions=read(R272/"q8-end-extensions.json")
        def endpoint_options(k):return sum(len(ends) for ends in extensions[roots[k]["shape"]].values())
        def seed_order(k):
            p=roots[k]["parent"];q=q9_path(k);b=[u-256 for u in q[len(p):]]
            return (len(q),word(b)!=word(best["B"]),data["roots"][k]["maximum"],endpoint_options(k),
                    -roots[k]["repair_start"]["needed_new_sites"],k)
        other=max(eligible,key=seed_order)
        seeds=[]
        for k in (first,other):
            q=q9_path(k);p=roots[k]["parent"];b=[u-256 for u in q[len(p):]]
            assert q==p[::-1]+[256+v for v in b] and hunt.original_audit.path_edges(q,9)==len(q)-1
            seeds.append(dict(root=k,parent_shape=roots[k]["shape"],partner_shape=word(b).hex(),
                        A=p,B=b,joined=q,edges=len(q)-1,fixed_endpoint_ceiling=data["roots"][k]["maximum"],
                        q8_tip_options=endpoint_options(k),nearest_donor=roots[k]["repair_start"]))
        write(HERE/"rebuild-seeds.json",dict(seeds=seeds,inequivalent_parent_shapes=True,
              distinct_partner_shapes=seeds[0]["partner_shape"]!=seeds[1]["partner_shape"]))
    print("Long Q9 shapes",dict(Counter(r["edges"] for r in paths.values())),"interval cones excluded",sum(r["ceiling"] is not None and r["ceiling"]<192 for r in own.values()),flush=True)

if __name__=="__main__":
    import sys
    if sys.argv[1]=="placements":recount()
    if sys.argv[1]=="catalogue":catalogue()
