"""Rebuild a single opposite arm while allowing its length to fall below the starting length."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
import sys

from prepare import HERE, MS, read, write, bank
sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
from exchange import variants, input_paths
from conditional import code

def explore(parent,starts,minimum,cap,known):
    blocked=sum(1<<v for v in parent[1:])
    paths=list(sorted(set(bytes(p) for p in starts)))
    indices={p:i for i,p in enumerate(paths)}
    pred=[-1]*len(paths)
    processed=0
    transitions=0
    while processed<len(paths) and len(paths)<cap:
        arm=paths[processed]
        before=len(paths)
        for group in variants(arm):
            for p,sites in group:
                if len(p)-1<minimum or sites&blocked:continue
                transitions+=1
                if p not in indices:
                    indices[p]=len(paths)
                    paths.append(p)
                    pred.append(processed)
        processed+=1
        if any(len(p)+len(parent)-1>=192 for p in paths[before:]):break
    counts=Counter(len(p)-1 for p in paths)
    h=sha256()
    for p in sorted(paths):
        h.update(bytes([len(p)])+p)
    extra={}
    best_id=max(range(len(paths)),key=lambda i:(len(paths[i]),-i))
    for i,p in enumerate(paths):
        if len(parent)+len(p)-1<190:continue
        seq=parent[::-1]+[v+256 for v in p]
        form=code(seq)
        if form not in known:
            bank.check_path(seq,9)
            extra.setdefault(sha256(form).hexdigest(),i)
    if extra:
        best_extra=max(extra.values(),key=lambda i:len(paths[i]))
        if len(paths[best_extra])>=len(paths[best_id]):
            best_id=best_extra
    route=[]
    i=best_id
    while i>=0:
        route.append(list(paths[i]))
        i=pred[i]
    seq=parent[::-1]+[v+256 for v in paths[best_id]]
    pairs=bank.check_path(seq,9)
    return dict(start=len(set(bytes(p) for p in starts)),expanded=processed,visited=len(paths),closed=processed==len(paths),
                moves=transitions,by_partner_length=counts,states_sha256=h.hexdigest(),
                outside_shapes={s:len(parent)+len(paths[i])-1 for s,i in extra.items()},best_path=seq,best_pairs=pairs,
                best_arm_route=route[::-1])

def main():
    ap=ArgumentParser()
    ap.add_argument("minimum",type=int)
    ap.add_argument("--limit",type=int,default=6000)
    opt=ap.parse_args()
    data=read(HERE/"cases.json")
    known={code(p) for _,p in input_paths()}
    dest=HERE/("single-"+str(opt.minimum)+".json")
    out=read(dest) if dest.exists() else dict(minimum=opt.minimum,limit=opt.limit,roots={})
    previous_limit=out["limit"]
    assert previous_limit<=opt.limit
    for row in out["roots"].values():
        row.setdefault("limit",previous_limit)
    out["limit"]=opt.limit
    for k,r in data["roots"].items():
        old=out["roots"].get(k)
        if not r["partners"] or old and (old["closed"] or old.get("limit",previous_limit)>=opt.limit):continue
        starts=list(r["partners"].values())
        assert all(len(p)==95 for p in starts) and len(r["parent"])==96
        rec=explore(r["parent"],starts,opt.minimum,opt.limit,known)
        rec["limit"]=opt.limit
        out["roots"][k]=rec
        write(dest,out)
        if len(rec["best_path"])>=193:
            write(HERE/"candidate-192.json",dict(parent=k,joined=rec["best_path"],pairs=rec["best_pairs"]))
            return
    print("Roots",len(out["roots"]),"closed",sum(r["closed"] for r in out["roots"].values()),
          "visited",sum(r["visited"] for r in out["roots"].values()),"best",max(len(r["best_path"])-1 for r in out["roots"].values()),
          "outside",sum(len(r["outside_shapes"]) for r in out["roots"].values()))

if __name__=="__main__":main()
