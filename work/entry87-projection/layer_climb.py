"""Increase a verified four-layer path by one vertex while all four layers may change."""
import argparse,json,random
from pathlib import Path
from layer_four import find,normalized_hint
from solve import defects,save


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("input",type=Path);p.add_argument("--rounds",type=int,default=120)
    p.add_argument("--seconds",type=float,default=5);p.add_argument("--radius",type=int,default=4)
    p.add_argument("--seed",type=int,default=19);p.add_argument("--sample",type=int,default=0);a=p.parse_args()
    source=json.loads(a.input.read_text());seen=set()
    if "results" in source:
        choices=sorted((r["vertices"] for r in source["results"] if r.get("vertices")),key=len,reverse=True)
        q=choices[a.sample]
    elif "best_path" in source:q=source["best_path"]
    else:q=source["vertices"]
    assert not defects(q)
    rng=random.Random(a.seed);ledger=[];original=len(q)-1;stage=0
    out=Path(f"layer-climb-{a.seed}-{a.radius}-{a.seconds}.json")
    for it in range(a.rounds):
        hints=normalized_hint(q);sizes=[len(hints[l]) for l in (0,1,3,2)]
        order=sorted(range(4),key=lambda i:(sizes[i],i));i=order[stage%4]
        if sizes[i]>=51:stage+=1;continue
        target=sizes.copy();target[i]+=1
        # Occasional transfers let a crowded layer give up a vertex while
        # another grows by two. Total size still increases by precisely one.
        if stage%8>=4:
            options=[k for k in range(4) if k!=i and target[k]>3]
            if target[i]<51:
                j=rng.choice(options);target[i]+=1;target[j]-=1
        radius=a.radius+2*((stage//8)%3)
        r=find(7,target,a.seconds,rng.randrange(1,100000000),hints,radius)
        qnew=r.pop("witness")
        if qnew:
            assert len(qnew)==len(q)+1 and not defects(qnew);q=qnew;stage=0
            print("improved",it,len(q)-1,target,flush=True)
        else:stage+=1
        ledger.append(dict(round=it,omit_per_layer=radius,**r))
        save(out,dict(input=a.input.name,starting_edges=original,best_path=q,best_edges=len(q)-1,rounds=ledger))
        if len(q)>=193:break
