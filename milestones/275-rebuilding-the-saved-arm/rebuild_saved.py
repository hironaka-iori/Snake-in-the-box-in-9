"""Rebuild the partner at the saved crossing and its three closest high-scoring controls."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from types import SimpleNamespace
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
R274=MS/"274-rebuilding-near-a-fixed-arm"
sys.path.insert(0,str(R274))
import face274 as face
from face274 import read,save
from union274 import literal,make_witness,transform
from known274 import isometry
MAIN="f89b051110afabb899a0b8477b95529b4081cd9da302082e0f89422455034531"
CONTROLS=("948d466c","c7fb24a4","8776c41d")
FOLDER=HERE/"opposite"

def resolve(keys,prefix):
    matches=[k for k in keys if k.startswith(prefix)]
    assert len(matches)==1,(prefix,matches)
    return matches[0]

def prepare():
    FOLDER.mkdir(exist_ok=True)
    union=read(R274/"union-paths.json");old=read(R274/"union274/plan.json")
    archive=read(R274/"union-placements.json")["roots"]
    inherited=read(R274/"union274/summary.json")["roots"]
    chosen=[MAIN,*[resolve(old["roots"],x) for x in CONTROLS]]
    shapes={old["roots"][k]["shape"]:union["shapes"][old["roots"][k]["shape"]] for k in chosen}
    assert all(r["source"]=="record2" for r in shapes.values())
    source=dict(seed=union["sources"]["record2"]["seed"],shapes=shapes)
    save(HERE/"saved-paths.json",source)
    plan=face.make_plan(source,1)
    inputs={name:sha256((R274/name).read_bytes()).hexdigest() for name in ("union-paths.json","union274/plan.json","union274/summary.json","union-placements.json")}
    plan["source_pins"]=inputs;plan["input_sha256"]=sha256((HERE/"saved-paths.json").read_bytes()).hexdigest()
    save(FOLDER/"plan.json",plan)
    placements={k:dict(parent=row["normalized"],best=archive[k]["best"]) for k,row in plan["roots"].items()}
    save(HERE/"saved-placements.json",dict(roots=placements))
    return plan,placements,inherited

def main():
    ap=ArgumentParser()
    ap.add_argument("action",choices=["prepare","search","audit"])
    ap.add_argument("--roots",nargs="+",default=[MAIN]);ap.add_argument("--target",type=int,default=192)
    ap.add_argument("--depth",type=int,default=0);ap.add_argument("--seconds",type=float,default=10)
    ap.add_argument("--standard",action="store_true")
    opt=ap.parse_args();plan,placements,prior=prepare()
    if opt.action=="prepare":return
    hunt=face.dependencies(MS)
    inherited=dict(roots={k:dict(maximum=prior[k]["maximum"],file="274-rebuilding-near-a-fixed-arm/union274/summary.json",row=["roots",k,"maximum"])
                          for k in plan["roots"]})
    if opt.action=="search":
        selected={resolve(plan["roots"],x) for x in opt.roots} if opt.roots!=["all"] else set(plan["roots"])
        opt.only=[i for i,g in enumerate(plan["groups"]) if g["keys"][0] in selected]
        opt.through=2;opt.parents=None;opt.refined_only=False
        face.search(FOLDER,plan,opt,hunt,inherited["roots"])
        return
    face.audit(FOLDER,plan,HERE,"saved",hunt,inherited)
    summary=read(FOLDER/"summary.json");bounds=summary["roots"]
    best={k:placements[k]["best"] for k in plan["roots"]}
    for f in sorted(FOLDER.glob("queries-*/*.json")):
        for row in read(f)["rows"].values():
            for k,q in row.get("literal_joins",{}).items():
                p=plan["roots"][k]
                assert q[:len(p["parent"])]==literal(p)[::-1]
                normalized=transform(q,isometry(literal(p),p["normalized"]))
                w=make_witness(p["normalized"],normalized)
                if w["edges"]>best[k]["edges"]:best[k]=w
    retained=HERE/"retained-replay.json"
    if retained.exists():
        for k,w in read(retained)["best"].items():
            assert w["joined"]==w["A"][::-1]+[256+v for v in w["B"]]
            if w["edges"]>best[k]["edges"]:best[k]=w
    for k,w in best.items():
        row=plan["roots"][k];p=literal(row);q=transform(w["joined"],isometry(row["normalized"],p))
        i=len(p);g=q[i:]
        assert q[:i]==p[::-1] and len(g)>0 and g[0]==256+row["raw_endpoint"]
        assert face.dependencies(MS).original_audit.path_edges(q,9)==w["edges"]
        bounds[k]["minimum"]=max(bounds[k]["minimum"],w["edges"])
        assert bounds[k]["minimum"]<=bounds[k]["maximum"]
        best[k]=dict(**w,original_joined=q,original_A=p,original_B=[x-256 for x in g],raw_crossing=row["raw_endpoint"])
    save(HERE/"constructions.json",best)
    save(HERE/"summary.json",dict(roots=bounds,targets=summary["targets"],primary=MAIN,source_pins=plan["source_pins"]))
    print([(k[:10],b["minimum"],b["maximum"]) for k,b in bounds.items()],flush=True)

if __name__=="__main__":main()
