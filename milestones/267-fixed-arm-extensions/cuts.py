"""Transport validated blockers to obtain compulsory sites in a rebuilt 95-edge arm."""
from prepare import HERE, MS, LAST, read, write, label,identifier,bank
from align import counter
from hashlib import sha256

def catalogue():
    paths=read(MS/"253-repeated-segment-growth/closure.json")["paths"]
    accepted=set(read(MS/"252-shorter-reference-segments/census-68.json")["all_ids"])
    assert read(MS/"252-shorter-reference-segments/replay-68-192.json")["all_excluded"] and accepted<=paths.keys()
    known={}
    def add_paths(cases,keys,tag):
        for k in keys:
            p=cases[k]
            if len(p)==97:
                for end,order in enumerate((p,p[::-1])):
                    normalized=label(order)[0]
                    known.setdefault(tuple(normalized[1:]),tag+"/"+k+":"+str(end))
    add_paths(paths,sorted(accepted),"252")
    focus=read(MS/"255-parity-exchange-arms/focus-closure.json")["paths"]
    closed=read(MS/"264-distant-component/summary.json")["closed_shapes"]
    add_paths(focus,closed,"264")
    short=read(LAST/"parents.json")["parents"]
    for k,r in read(LAST/"partner-189.json")["roots"].items():
        assert r["0"]["status"]=="excluded"
        known[tuple(short[k]["parent"][1:])]="266/"+k
    for k,r in read(MS/"262-common-forbidden-sites/groups.json").items():
        if r["status"]=="excluded":
            known[tuple(sorted(r["blocked"]))]="262/"+k
    return known

def at_least(columns,bound):
    equal=bank.ALL_MAPS
    higher=0
    for j in reversed(range(len(columns))):
        if bound & (1<<j):
            equal &= columns[j]
        else:
            higher |= equal & columns[j]
            equal &=~columns[j]
    return higher|equal

def main():
    data=read(HERE/"cases.json")
    sources=catalogue()
    images=list(bank.permutation_images())
    out={}
    for name,g in data["groups"].items():
        core=set(g["blocked"])
        candidates={}
        for target,rank in g["ranks"].items():
            parent=set(bytes(data["roots"][target]["parent"][1:]).translate(images[rank]))
            flags=bank.allowed_maps([0]+sorted(set(range(1,256))-parent),images)
            for mask,source in sources.items():
                totals=counter.columns(flags[v] for v in mask)
                live=at_least(totals,len(mask)-5)
                while live:
                    low=live&-live
                    perm=low.bit_length()-1
                    live^=low
                    moved=set(bytes(mask).translate(images[perm]))
                    assert len(moved-parent)<=5
                    sites=tuple(sorted(moved-core))
                    candidates.setdefault(sites,dict(source=source,rank=perm,sites=list(sites)))
        minimal=[]
        for vs,cut in sorted(candidates.items(),key=lambda p:(len(p[0]),p[0])):
            v=set(vs)
            if not any(prior<=v for prior in minimal):
                minimal.append(v)
        out[name]=[candidates[tuple(sorted(v))] for v in minimal]
    write(HERE/"cuts.json",out)
    print("Cuts",sum(map(len,out.values())),"groups with cuts",sum(bool(z) for z in out.values()),"empty hits",sum(any(not c["sites"] for c in z) for z in out.values()))

if __name__=="__main__":
    main()
