"""Search against the forbidden sites shared by two nearby arms."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from rebuild_saved import HERE, MS, face, read, save, resolve
from union274 import transform
from known274 import isometry

PAIRS={"93":("f89b","948d"),"94":("c7fb","8776")}

def data():
    plan=read(HERE/"opposite/plan.json")["roots"]; placed=read(HERE/"saved-placements.json")["roots"]
    out={}
    for label,prefixes in PAIRS.items():
        keys=[resolve(plan,pre) for pre in prefixes]
        A=[plan[k]["parent"] for k in keys]
        assert all(p[0]==0 for p in A)
        common=set(A[0])&set(A[1])
        B=[]
        for k in keys:
            p=plan[k];q=transform(placed[k]["best"]["joined"],isometry(p["normalized"],p["parent"]))
            assert q[:len(p["parent"])]==p["parent"][::-1]
            B.append([v-256 for v in q[len(p["parent"]):]])
        assert B[0]==B[1] and set(B[0])&common=={0}
        out[label]=dict(roots=keys,relative_parents=A,common=sorted(common-{0}),omitted=[sorted(set(a)-common) for a in A],
                        known_partner=B[0],crossing=plan[keys[0]]["raw_endpoint"])
    return out

def main():
    ap=ArgumentParser();ap.add_argument("action",choices=["search","audit"])
    ap.add_argument("--pair",choices=PAIRS,default="93");ap.add_argument("--length",type=int,default=98)
    ap.add_argument("--depth",type=int,default=0);ap.add_argument("--seconds",type=float,default=5)
    opt=ap.parse_args();families=data();hunt=face.dependencies(MS);hunt.search.base_model=hunt.deficit.model
    folder=HERE/"shared";folder.mkdir(exist_ok=True);file=folder/"queries.json"
    ledger=read(file) if file.exists() else {}
    if opt.action=="search":
        x=families[opt.pair];p=[0]+x["common"];k=opt.pair
        lower=len(x["known_partner"])-1
        if opt.length<=lower:raise ValueError("Requested partner already constructed")
        rows=ledger.setdefault(k,{}).setdefault(str(opt.length),{})
        with TemporaryDirectory(prefix="q9-r275-common-") as temp:
            tmp=Path(temp);tools=hunt.rebuild.masks.compilers(tmp)
            def visit(prefix):
                addr=",".join(map(str,prefix));old=rows.get(addr,{})
                if old.get("status") in ("witness","excluded"):return
                masks=hunt.translate_domains({k:p},prefix)
                if not masks:return
                if len(prefix)<=opt.depth:
                    for v in hunt.legal_next(prefix):visit(prefix+[v])
                    return
                blocked=masks[k]
                hunt.rebuild.model=hunt.family_model([blocked])
                row=hunt.rebuild.solve(folder,tmp,tools,blocked,opt.length+1-len(prefix),[0],old.get("cycles",[]),[],opt.seconds)
                row["encoding"]="parity-deficit"
                if row["status"]=="witness":
                    b=prefix[:-1]+[v^prefix[-1] for v in row["path"]]
                    assert hunt.original_audit.path_edges(b,8)==opt.length and not set(b)&set(x["common"])
                    row["partner"]=b
                rows[addr]=row;save(file,ledger)
                print(k,opt.length,addr,row["status"],flush=True)
            visit([0])
        return
    hunt.original_audit.HERE=folder
    caps={};checked=Counter()
    with TemporaryDirectory(prefix="q9-r275-common-replay-") as temp:
        tmp=Path(temp);checker=hunt.rebuild.masks.compilers(tmp)[0]
        for k,facts in families.items():
            blocked=set(facts["common"]);lo=len(facts["known_partner"])-1;hi=98
            witnesses=[facts["known_partner"]]
            for nstr,rows in ledger.get(k,{}).items():
                n=int(nstr);excluded=set()
                for addr,row in rows.items():
                    prefix=list(map(int,addr.split(",")));end=prefix[-1]
                    assert hunt.original_audit.path_edges(prefix,8)==len(prefix)-1 and prefix[0]==0
                    assert set(prefix).isdisjoint(blocked)
                    mask={u^end for u in range(256) if u in blocked or (u!=end and any((u^v).bit_count()<=1 for v in prefix[:-1]))}
                    hunt.original_audit.replay([mask],n+1-len(prefix),row,tmp,checker)
                    checked[row["status"]]+=1
                    if row["status"]=="excluded":excluded.add(tuple(prefix))
                    if row["status"]=="witness":
                        b=prefix[:-1]+[u^end for u in row["path"]]
                        assert b==row["partner"] and hunt.original_audit.path_edges(b,8)==n and set(b).isdisjoint(blocked)
                        witnesses.append(b);lo=max(lo,n)
                depth=max(map(len,excluded),default=0)
                def closed(prefix):
                    if tuple(prefix) in excluded:return True
                    if len(prefix)>=depth:return False
                    return all(closed(prefix+[v]) for v in hunt.next_sites(prefix,blocked|{0}))
                if closed([0]):hi=min(hi,n-1)
            assert lo<=hi
            caps[k]=dict(**facts,partner_minimum=lo,partner_maximum=hi,witnesses=witnesses)
    save(folder/"summary.json",dict(families=caps,checked=checked))
    print("Shared-site capacities",[(k,r["partner_minimum"],r["partner_maximum"]) for k,r in caps.items()],flush=True)

if __name__=="__main__":main()
