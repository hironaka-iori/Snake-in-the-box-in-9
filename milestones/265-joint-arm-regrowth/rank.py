"""Rank candidate crossings by verified donor placements outside earlier exclusions."""
from pathlib import Path
from collections import Counter
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"260-donor-intersections"))
from census import bank,load,save,digest

def reference_data():
    pins={}
    def read(relative):
        f=MS/relative
        pins[relative]=digest(f)
        return load(f)
    root_table=read("253-repeated-segment-growth/placements.json")["cases"]
    parents=read("253-repeated-segment-growth/closure.json")["paths"]
    closed=set(read("264-distant-component/summary.json")["closed_shapes"])
    closed.update(read("259-four-exchange-component/component.json")["max_four_neighbours"])
    closed.update(read("257-three-exchange-parents/partner-input.json")["shapes"])
    closed.update(read("252-shorter-reference-segments/census-68.json")["all_ids"])
    covered=read("253-repeated-segment-growth/group-replay.json")["covered"]
    transports=read("253-repeated-segment-growth/transports.json")["results"]
    skipped={(r["shape"],r["end"]) for r in transports if r["witnesses"] or r["root_id"] in covered}
    transfers=read("262-common-forbidden-sites/transfer.json")
    def code(s):
        steps=[v^u for v,u in zip(s,s[1:])]
        order=list(dict.fromkeys(steps))
        return bytes(order.index(v) for v in steps)
    avoided=set()
    for tag in transfers["covered"]:
        shape,end=tag.split(":")
        path=transfers["reference_paths"][shape]
        avoided.add(code(path if end=="0" else path[::-1]))
    donors={}
    def add(p):
        c=min(code(p),code(p[::-1]))
        if c not in donors:
            bank.check_path(p,8)
            donors[c]=p
    for rel in ("252-shorter-reference-segments/construct-68.json","253-repeated-segment-growth/remote-arms.json",
        "254-distant-arm-partners/aggregate.json","254-distant-arm-partners/constructive.json",
        "255-parity-exchange-arms/constructive.json","257-three-exchange-parents/constructed-51.json",
        "261-rerouted-partners/intervals.json","264-distant-component/expanded-constructions.json"):
        cases=read(rel)["cases"]
        for row in cases.values() if isinstance(cases,dict) else cases:
            add(row["partner"])
    for row in read("248-rooted-arm-capacity/attainers.json")["records"]:
        for sample in row["paths"]: add(sample["path"])
    # Apply every earlier complete full-parent exclusion in the common source bank
    # by canonical rooted order; both ends of each fully excluded shape are covered above.
    sys.path.insert(0,str(MS/"264-distant-component"))
    from endpoints import evidence,rooted_axes
    _,old,files=evidence()
    pins.update({f.relative_to(MS).as_posix():digest(f) for f in files})
    avoided.update(bytes(rooted_axes(mask)[0]) for mask in old.values() if len(mask)==96)
    out={}
    for r in root_table:
        k,e=r["id"],r["end"]
        P=parents[k][::-1] if e else parents[k]
        if len(P)!=97 or k in closed or (k,e) in skipped or code(P) in avoided:continue
        P=[v^P[0] for v in P]
        B=max(r["banks"].values(),key=lambda x:x["partner_edges"])["partner"]
        out[k+":"+str(e)]=(P,B)
    return out,list(donors.values()),pins

def main():
    targets,donors,pins=reference_data()
    images=list(bank.permutation_images())
    words,origins=bank.donor_suffixes(donors)
    dest=HERE/"placements.json"
    data=load(dest) if dest.exists() else dict(pins=pins,donors=len(donors),directed_words=len(words),cases={})
    if data["pins"]!=pins:raise ValueError("Source differs")
    for tag,(P,B) in targets.items():
        if tag in data["cases"]:continue
        maps=bank.allowed_maps(P,images)
        fit=bank.longest(words,maps)
        donor=bank.make_witness(donors,origins[fit[1]],fit,P)
        Q=max((B,donor["partner"]),key=len)
        seq=P[::-1]+[256+v for v in Q]
        data["cases"][tag]=dict(A=P,B=Q,prior=96+len(B),donor=96+len(donor["partner"]),
            edges=len(seq)-1,pairs=bank.check_path(seq,9))
        if len(data["cases"])%15==0:save(dest,data)
    save(dest,data)
    print("Eligible",len(targets),"donors",len(donors),"words",len(words))
    print(Counter(r["edges"] for r in data["cases"].values()).most_common())
    print("Leaders",[(k[:8]+k[-2:],r["edges"]) for k,r in sorted(data["cases"].items(),key=lambda x:-x[1]["edges"])[:12]])

if __name__=="__main__":main()
