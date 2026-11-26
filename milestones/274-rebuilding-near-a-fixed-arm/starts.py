"""Select the shorter arms of the archived 191-edge joins and an independent Round 273 parent."""
from near import HERE, MS, read, write, valid, shape
def main():
    earlier=MS/"266-rebuilding-one-arm"
    prior=read(earlier/"parents.json")["parents"]
    attainers=read(earlier/"summary.json")["archived_attainers"]
    selected={}
    for i,(k,indices) in enumerate(sorted(attainers.items()),1):
        t=prior[k];a=t["parent"]
        eligible=[(key,b) for key,b in t["partners"].items() if key.startswith("191-") and len(b)==97]
        ref,b=min(eligible)
        assert len(a)==95 and int(ref.split("-")[1]) in indices
        q=a[::-1]+[v+256 for v in b];valid(q,9)
        selected["record"+str(i)]=dict(seed=a,other=b,reference=q,root=k,example=ref,covered_examples=indices)
    assert len({shape(x["seed"]) for x in selected.values()})==5
    assert len({j for x in selected.values() for j in x["covered_examples"]})==25
    source=MS/"273-partners-of-rebuilt-arms/extensions-188.json"
    if source.is_file():
        pool=read(source)["constructions"]
        row=next(r for r in pool if not r["archive_matches"])
        a,b=row["A"],row["B"]
        q=a[::-1]+[v+256 for v in b];valid(q,9)
        assert q==row["joined"]
        selected["rebuilt97"]=dict(seed=a,other=b,reference=q,source_96_root=row["source_96_root"])
    write(HERE/"selected-start.json",selected)
    print("Selected seeds",[(k,len(v["seed"])-1,len(v["reference"])-1) for k,v in selected.items()])
if __name__=="__main__":main()
