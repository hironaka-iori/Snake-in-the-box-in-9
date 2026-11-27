"""Transport the shared-site bounds using every possible placement of the 90-edge segment."""
from collections import Counter
from hashlib import sha256
from rebuild_saved import HERE,R274,MS,face,read,save,isometry
from known274 import normalize

def main():
    facts=read(HERE/"shared/summary.json")["families"]
    union=read(R274/"union274/plan.json")["roots"]
    bounds=read(R274/"union274/summary.json")["roots"]
    direct=read(HERE/"summary.json")["roots"]
    by_root={};geometry={}
    for tag,info in facts.items():
        capacities=[info["partner_maximum"]]
        for file in (HERE/"shared").glob(f"forced-replay-{tag}-*.json"):
            res=read(file)
            if res["status"]=="excluded":capacities.append(int(file.stem.rsplit("-",1)[1])-1)
        cap=min(capacities)
        assert info["partner_minimum"]<=cap
        p,q=info["relative_parents"];j=3 if tag=="93" else 4
        core=p[j:]
        assert core==q[j:][::-1] and len(core)==91
        extras=set(info["common"])-set(core)
        assert len(extras)==(0 if tag=="93" else 1)
        assert set(core)|extras==set(info["common"]) and len(normalize(core)[2])==8
        geometry[tag]=dict(core=core,extra=sorted(extras),core_edges=90,seed_roots=info["roots"],
                           partner_maximum=cap,initial_routes=[p[:j+1],q[:j+1]])
        for k,row in union.items():
            F=row["parent"];sites=set(F[1:])
            for start in range(len(F)-len(core)+1):
                window=F[start:start+len(core)]
                for direction,c in enumerate((core,core[::-1])):
                    if normalize(c)[0]!=normalize(window)[0]:continue
                    m=isometry(c,window);axes=m["axes"]
                    def perm(v):return sum(1<<axes[i] for i in range(8) if v&1<<i)
                    if m["reference_start"]!=perm(m["literal_start"]):continue
                    if any(perm(v) not in sites for v in extras):continue
                    assert set(map(perm,info["common"]))<=sites
                    ceil=len(F)+cap
                    evidence=dict(pair=tag,start=start,direction=direction,axes=axes,ceiling=ceil)
                    by_root.setdefault(k,[]).append(evidence)
    derived={k:dict(before=bounds[k]["maximum"],ceiling=min(v["ceiling"] for v in ev),
               minimum=max(bounds[k]["minimum"],direct.get(k,{}).get("minimum",0)),certificate=ev) for k,ev in by_root.items()}
    assert all(r["minimum"]<=r["ceiling"] for r in derived.values())
    out=dict(source_sha256=sha256((R274/"union274/plan.json").read_bytes()).hexdigest(),geometry=geometry,
             roots=derived,matched=len(by_root),improved=sum(r["ceiling"]<r["before"] for r in derived.values()),
             newly_excluded_192=sum(r["ceiling"]<192<=r["before"] for r in derived.values()))
    save(HERE/"shared/transport.json",out)
    print("Shared cores",out["matched"],"sharpened",out["improved"],"new 192 exclusions",out["newly_excluded_192"],flush=True)
if __name__=="__main__":main()
