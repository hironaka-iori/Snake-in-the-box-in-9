"""Rebuild a near fitting donor, or extend a valid opposite arm by retaining sites."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from search_partners import HERE, cases, read, write, hunt
from retain import retention_model,checked_join


def main():
    ap=ArgumentParser()
    ap.add_argument("--top",type=int,default=12)
    ap.add_argument("--target",type=int,default=190)
    ap.add_argument("--extra",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=3)
    ap.add_argument("--seed",choices=["near","joined"],default="near")
    ap.add_argument("--audit",action="store_true")
    args=ap.parse_args()
    roots=cases();dest=HERE/"donor-repairs.json"
    ledger=read(dest) if dest.exists() else {}
    if args.seed=="near":
        order=sorted(roots,key=lambda k:(roots[k]["repair_start"]["needed_new_sites"],-roots[k]["best"]["edges"],k))
    else:
        order=sorted(roots,key=lambda k:(-roots[k]["best"]["edges"],roots[k]["repair_start"]["needed_new_sites"],k))
    order=list(ledger) if args.audit else order[:args.top]
    maps=list(hunt.bank.permutation_images())
    found={}
    with TemporaryDirectory() as td:
        tmp=Path(td);tools=hunt.rebuild.masks.compilers(tmp)
        for k in order:
            r=roots[k];p=r["parent"];blocked=set(p[1:])
            rec=r["repair_start"];near=rec["donor"]
            vertices=[0]
            for axis in bytes.fromhex(rec["word"]):vertices.append(vertices[-1]^(1<<axis))
            assert near==list(bytes(vertices).translate(maps[rec["rank"]]))
            assert rec["intersections"]==sorted(set(near)&blocked)
            rows=ledger.setdefault(k,{})
            valid={tuple(r["best"]["B"])}
            for row in rows.values():
                result=row["result"]
                if result["status"]=="witness":
                    assert checked_join(p,result["path"])==result["joined"]
                    valid.add(tuple(result["path"]))
            if args.audit:
                for row in rows.values():
                    seed=row["seed"];budget=row["budget"];target=row["target"];result=row["result"]
                    assert seed==near if row["source"]=="near" else tuple(seed) in valid
                    keep=set(seed)-blocked;n=target-len(p)
                    cm,selected=hunt.deficit.model(blocked,n,[0],result["cycles"],[])
                    cm.at_most([-selected[u] for u in range(1,256) if u in keep],budget)
                    f=tmp/"repair-audit.cnf"
                    assert cm.save(f)==result["cnf"] and len(cm.clauses)==result["clauses"]
                    if result["status"]=="excluded":
                        file=HERE/result["proof"]
                        assert sha256(file.read_bytes()).hexdigest()==result["compressed"]
                        assert hunt.rebuild.masks.p.check_proof(f,file,tools[0])==result["replay"]
                    elif result["status"]=="witness":
                        q=result["path"]
                        assert len(q)==n+1 and not set(q)&blocked and len(keep-set(q))<=budget
                        if k not in found or found[k]["edges"]<target:
                            found[k]=dict(edges=target,joined=result["joined"],extra_omitted=len(keep-set(q)),
                                          forced_omitted=len(set(seed)&blocked),seed=seed)
                continue
            target=args.target
            seed=near if args.seed=="near" else list(max(valid,key=lambda b:(len(b),b)))
            n=target-len(p)
            if args.seed=="joined" and len(seed)>n:continue
            keep=set(seed)-blocked
            budget=args.extra+max(0,len(keep)-(n+1))
            tag=f"{args.seed}-{target}-{budget}-{sha256(bytes(seed)).hexdigest()[:10]}"
            old=rows.get(tag,{}).get("result",{})
            if old.get("status") in ("excluded","witness"):continue
            hunt.rebuild.model=retention_model(keep,budget)
            result=hunt.rebuild.solve(HERE,tmp,tools,blocked,n,[0],old.get("cycles",[]),[],args.seconds)
            if result["status"]=="witness":
                result["joined"]=checked_join(p,result["path"])
                assert len(result["joined"])==target+1
                if target>=192:write(HERE/"candidate-192.json",result["joined"])
            rows[tag]=dict(source=args.seed,seed=seed,target=target,budget=budget,result=result)
            write(dest,ledger)
            print(k[:10],args.seed,"forced",len(set(seed)&blocked),"additional",budget,target,result["status"],flush=True)
            if (HERE/"candidate-192.json").exists():break
    if args.audit:
        write(HERE/"retained-site-replay.json",found)
        print("Repairs",Counter(r["result"]["status"] for data in ledger.values() for r in data.values()),
              "positive roots",len(found),flush=True)

if __name__=="__main__":main()
