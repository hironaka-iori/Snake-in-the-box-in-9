"""Place the complete 92-edge partner or its longest crossing-side prefix at every fixed endpoint."""
from collections import Counter
from itertools import permutations
from hunt import HERE, bank, cases, original_audit, read, write


def main():
    roots=cases()
    seeds=[r["partner"] for r in read(HERE/"long-joins.json")["witnesses"] if r["edges"]==189]
    assert len(seeds)==2 and len({original_audit.shape(q) for q in seeds})==1
    donor=seeds[0]
    orders=[bytes(x^p[0] for x in p) for p in (donor,donor[::-1])]
    images=list(bank.permutation_images())
    dims=list(permutations(range(8)))
    assert all(all(image[1<<i]==1<<axes[i] for i in range(8)) for image,axes in zip(images,dims,strict=True))
    masks=[[sum(1<<v for v in q.translate(image)[1:]) for image in images] for q in orders]
    by_root={}; lengths=Counter(); improved=0
    for k,r in roots.items():
        p=r["parent"];forbidden=sum(1<<v for v in p[1:])
        allowed=bank.allowed_maps(p,images)
        best=None;counts=[]
        for d,q in enumerate(orders):
            live=bank.ALL_MAPS;length=0
            for v in q[1:]:
                updated=live&allowed[v]
                if not updated:break
                live=updated;length+=1
            fits=live.bit_count() if length==len(q)-1 else 0
            assert fits==sum((forbidden&m)==0 for m in masks[d])
            counts.append(fits)
            if best is None or length>best["partner_edges"]:
                rank=(live&-live).bit_length()-1; axes=dims[rank]
                b=[sum(1<<axes[i] for i in range(8) if v&(1<<i)) for v in q[:length+1]]
                joined=p[::-1]+[256+v for v in b]
                n=original_audit.path_edges(joined,9)
                assert n==len(p)+length
                best=dict(source_order=d,rank=rank,partner_edges=length,edges=n,joined=joined)
        best["full_placements_by_order"]=counts
        by_root[k]=best;lengths[best["edges"]]+=1;improved+=best["edges"]>r["best"]["edges"]
    out=dict(donor=donor,roots=by_root,trials=len(roots)*len(images)*len(orders),longest=max(lengths),
             best_lengths=lengths,roots_improved_over_round270=improved,
             full_donor_roots=sum(bool(sum(r["full_placements_by_order"])) for r in by_root.values()))
    write(HERE/"new-donor.json",out)
    print({k:v for k,v in out.items() if k not in ("donor","roots")},flush=True)


if __name__=="__main__":
    main()
