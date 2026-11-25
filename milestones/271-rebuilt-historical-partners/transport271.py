"""Transport previously checked bounds on a rooted Q8 partner by inclusion of blocked sites."""
from hashlib import sha256
from itertools import permutations
import json
from opposite import bank, write


def catalogue(ms):
    pins, refs = {}, {}
    def load(name):
        data=(ms/name).read_bytes()
        pins[name]=sha256(data).hexdigest()
        return json.loads(data)
    def take(name, sites, threshold):
        assert 0 not in sites and len(set(sites))==len(sites) and threshold>0
        refs[name]=(tuple(sorted(sites)),threshold)
    def orientations(name,p,threshold):
        for i,q in enumerate((p,p[::-1])):
            take(name+"/"+str(i),[v^q[0] for v in q[1:]],threshold)
    d248=load("248-rooted-arm-capacity/aggregate.json")
    pairs=load("246-eight-dimensional-parents/comparison.json")["one_crossing_pairs"]
    for row in d248["endpoint94"]:
        case,end=row["case"]
        arm=next(r["long"] for r in pairs if r["seed"]==case)
        p=arm if end==0 else arm[::-1]
        if row["upper_excluded"]:
            take(f"248/{case}/{end}",[v^p[0] for v in p[1:]],94)
    assert load("252-shorter-reference-segments/replay-68-192.json")["all_excluded"]
    ids=load("252-shorter-reference-segments/census-68.json")["all_ids"]
    old=load("253-repeated-segment-growth/closure.json")["paths"]
    for k in ids:
        p=old[k]
        orientations("252/"+k,p,192-len(p))
    for k,r in load("262-common-forbidden-sites/groups.json").items():
        if r["status"]=="excluded":take("262/"+k,r["blocked"],95)
    ids=load("264-distant-component/summary.json")["closed_shapes"]
    old=load("255-parity-exchange-arms/focus-closure.json")["paths"]
    for k in ids:
        p=old[k]
        assert len(p)==97
        orientations("264/"+k,p,95)
    parents=load("266-rebuilding-one-arm/parents.json")["parents"]
    for target in (189,192):
        for k,rows in load(f"266-rebuilding-one-arm/partner-{target}.json")["roots"].items():
            if rows["0"]["status"]=="excluded":
                p=parents[k]["parent"]
                take(f"266/{target}/"+k,p[1:],target-len(p))
    prior=load("267-fixed-arm-extensions/cases.json")["roots"]
    for k in load("267-fixed-arm-extensions/summary.json")["coverage"]:
        p=prior[k]["parent"]
        take("267/"+k,p[1:],192-len(p))
    targets=load("268-archived-94-arms/summary.json")["targets"]
    for n,r in targets.items():
        for k in r["covered"]:take("268/"+n+"/"+k,parents[k]["parent"][1:],int(n))
    return refs,pins


def build_transfers(here,ms,cases,images):
    records,pins=catalogue(ms)
    # Try the strongest bound first. Repeated masks need only their best threshold.
    ordered=sorted(records,key=lambda k:(records[k][1],len(records[k][0]),k))
    seen=set()
    names=[]
    for name in ordered:
        mask,_=records[name]
        if mask not in seen:
            seen.add(mask)
            names.append(name)
    out={}
    for k,row in cases.items():
        F=set(row["parent"][1:])
        flags=bank.allowed_maps([0]+sorted(set(range(1,256))-F),images)
        for name in names:
            mask,q=records[name]
            if len(mask)>len(F) or q>98:continue
            live=bank.ALL_MAPS
            for v in mask:
                live &= flags[v]
                if not live:break
            if live:
                rank=(live & -live).bit_length()-1
                assert set(bytes(mask).translate(images[rank]))<=F
                out[k]=dict(source=name,rank=rank,partner_threshold=q,ceiling=len(row["parent"])+q-1)
                break
    write(here/"transfers.json",dict(sources=pins,root_cases=len(cases),roots=out))
    print("Transported whole-root blockers",len(out),"of",len(cases),
          "excluding 192",sum(r["ceiling"]<192 for r in out.values()),flush=True)
    return out


def verify_transfers(here,ms,cases):
    source,pins=catalogue(ms)
    saved=json.loads((here/"transfers.json").read_bytes())
    assert saved["sources"]==pins and saved["root_cases"]==len(cases)
    perms=list(permutations(range(8)))
    out={}
    for k,row in saved["roots"].items():
        mask,q=source[row["source"]]
        axes=perms[row["rank"]]
        forbidden=set(cases[k]["parent"][1:])
        for v in mask:
            assert sum(1<<axes[i] for i in range(8) if (v>>i)&1) in forbidden
        cap=len(cases[k]["parent"])+q-1
        assert q==row["partner_threshold"] and row["ceiling"]==cap
        out[k]=cap
    return out
