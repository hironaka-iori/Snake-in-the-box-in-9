"""Reconcile the independent geometry, bounds and archived witnesses for the completed round."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import sys
from inputs276 import HERE,MS,read,save,valid,canonical
sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
from exchange import input_paths

def main():
    data=read(HERE/"input-arms.json");bounds=read(HERE/"endpoint-results.json")
    scans={};shapes=set()
    for f in sorted(HERE.glob("anchors-*.json")):
        d=read(f);assert d["complete"]
        labs=sum(v["first"]["paths"] for v in d["seeds"].values())
        cases=sum(v["first"]["setups"] for v in d["seeds"].values())
        for s,r in d["shapes"].items():assert valid(r["path"],8)==4851 and canonical(r["path"])==s
        shapes.update(d["shapes"])
        scans[f.name]=dict(inputs=len(d["seeds"]),cases=cases,attaining_seeds=sum(bool(v["shapes"]) for v in d["seeds"].values()),labelled_seed_path_pairs=labs,shapes=sorted(d["shapes"]))
    for f in sorted(HERE.glob("site-neighbours-*.json")):
        d=read(f);shapes.update(d["shapes"]);scans[f.name]=dict(levels={k:{p:r[p] for p in ("masks","nonempty","labelled")} for k,r in d["levels"].items()},shapes=sorted(d["shapes"]))
    sphere=read(HERE/"site-distance.json");replay=read(HERE/"site-distance-replay.json")
    assert sha256((HERE/"site-distance.json").read_bytes()).hexdigest()==replay["ledger_sha256"]
    p=data["known_endpoints"]["0"]["parent"];p_set=set(p)
    nearby=[]
    for level,row in sphere.items():
        for q in row["paths"]:
            assert len(q)==len(p) and len(p_set-set(q))==int(level) and valid(q,8)==4851
            shapes.add(canonical(q));nearby.append((int(level),q))
    orbit=read(HERE/"isometry-orbit.json");d=orbit["minimum_positive"];a=orbit["permutation"];t=orbit["translation"]
    image=[t^sum(1<<a[j] for j in range(8) if (v>>j)&1) for v in p]
    assert image==orbit["path"] and len(p_set-set(image))==d and d<=replay["complete_through"]
    assert len([1 for lev,q in nearby if lev<=d])==1 and any(set(q)==set(image) and lev==d for lev,q in nearby)
    assert all(canonical(q)==data["reference_shape"] for lev,q in nearby if lev<=replay["complete_through"])
    shapes.add(data["reference_shape"])
    assert shapes=={r["shape"] for r in bounds.values()}
    exact={};winners={}
    for k,r in bounds.items():
        w=r["best"];assert w["joined"]==r["parent"][::-1]+[256+u for u in w["partner"]]
        assert valid(w["joined"],9)==w["pairs"] and len(w["joined"])==r["minimum"]+1
        exact[k]=dict(lower=r["minimum"],upper=r["maximum"],partner_lower=r["minimum"]-99,partner_upper=r["maximum"]-99)
        winners[k]=canonical(w["joined"])
    matches={k:[] for k in winners}
    for label,p in input_paths():
        for n in {v["minimum"] for v in bounds.values()}:
            if len(p)<=n:continue
            codes={s for k,s in winners.items() if bounds[k]["minimum"]==n}
            for i in range(len(p)-n):
                c=canonical(p[i:i+n+1])
                if c in codes:
                    for k,s in winners.items():
                        if c==s:matches[k].append([label,i])
    best=max(bounds,key=lambda k:bounds[k]["minimum"]);save(HERE/"best-join.json",dict(root=best,**bounds[best]["best"]))
    summary=dict(fixed_endpoints=exact,archive_matches=matches,distinct_best_shapes=len(set(winners.values())),best_root=best,
        best_length=bounds[best]["minimum"],family_join_lower=max(r["minimum"] for r in bounds.values()),
        family_join_upper=max(r["maximum"] for r in bounds.values()),new_98_shapes=sorted(shapes-{data["reference_shape"]}),catalogues=scans)
    summary.update(site_distance=dict(complete_through=replay["complete_through"],minimum_distinct=d,
        closest_removed=orbit["removed"],closest_added=orbit["added"],isometry=dict(permutation=a,translation=t),
        nearest_multiplicity=orbit["histogram"][str(d)]//orbit["stabilizer"],labelled_orbit=orbit["orbit"],
        remaining_radius_status={k:e["status"] for k,e in sphere.items() if int(k)>replay["complete_through"]}))
    save(HERE/"summary.json",summary);print("Final endpoint bounds",exact,"best",summary["best_length"],"optimal shapes",len(shapes),flush=True)
if __name__=="__main__":main()
