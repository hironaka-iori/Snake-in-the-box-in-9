"""Regrow a complete opposite arm while keeping as many sites of a verified start as possible."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from hashlib import sha256
import json,sys
from hunt import HERE,cases,read,write,rebuild,original_audit,deficit

def retention_model(seed, budget):
    def build(blocked, count, prefix, cycles, seen):
        model, selected = deficit.model(blocked,count,prefix,cycles,seen)
        model.at_most([-selected[v] for v in sorted(seed) if v],budget)
        return model,selected
    return build

def checked_join(parent,partner):
    path=parent[::-1]+[256+v for v in partner]
    assert set(parent)&set(partner)=={0}
    assert original_audit.path_edges(path,9)==len(path)-1
    return path

def main():
    ap=ArgumentParser()
    ap.add_argument("--omissions",type=int,nargs="+",default=[4,8,16])
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--top",type=int,default=3)
    ap.add_argument("--history",action="store_true")
    ap.add_argument("--audit",action="store_true")
    args=ap.parse_args()
    roots=cases()
    for f in sorted(HERE.glob("matched-*.json")):
        for tag,r in read(f).items():
            w=r["best"];k=tag.split(":")[0]
            if w and w["edges"]>roots[k]["best"]["edges"]:
                assert roots[k]["parent"]==w["A"] and checked_join(w["A"],w["B"])==w["joined"]
                roots[k]["best"]=w
    ordered=sorted(roots,key=lambda k:(-roots[k]["best"]["edges"],k))
    dest=HERE/"retained-sites.json"
    ledger=read(dest) if dest.is_file() else {}
    using=[k for k in ordered if not args.history or roots[k]["history"]][:args.top]
    if args.audit:using=list(ledger)
    with TemporaryDirectory() as d:
        tmp=Path(d);tools=rebuild.masks.compilers(tmp)
        for k in using:
            parent=roots[k]["parent"];start=roots[k]["best"]["B"];blocked=set(parent[1:])
            data=ledger.setdefault(k,dict(parent=parent,start=start,queries=[],best=start))
            assert data["start"]==start and data["parent"]==parent
            if args.audit:
                valid={tuple(start)}
                for row in data["queries"]:
                    seed=row["seed"];budget=row["omissions"];result=row["result"];size=row["partner_length"]
                    assert tuple(seed) in valid and result["prefix"]==[0] and size==len(seed)
                    cnf,sel=deficit.model(blocked,size,[0],result["cycles"],[])
                    missing=[-sel[v] for v in range(1,256) if v in seed]
                    cnf.at_most(missing,budget)
                    f=tmp/"audit.cnf";assert cnf.save(f)==result["cnf"] and len(cnf.clauses)==result["clauses"]
                    if result["status"]=="excluded":
                        proof=HERE/result["proof"]
                        assert sha256(proof.read_bytes()).hexdigest()==result["compressed"] and rebuild.masks.p.check_proof(f,proof,tools[0])==result["replay"]
                    if result["status"]=="witness":
                        p=result["path"]
                        assert len(p)==size+1 and len(set(seed)-set(p))<=budget
                        assert checked_join(parent,p)==row["joined"]
                        valid.add(tuple(p))
                assert tuple(data["best"]) in valid and len(data["best"])==max(map(len,valid))
                continue
            for budget in args.omissions:
                while True:
                    seed=data["best"];size=len(seed)
                    if (len(parent)-1)+1+size>192:break
                    if any(r["seed"]==seed and r["omissions"]>=budget and r["result"]["status"]=="excluded" for r in data["queries"]):break
                    rebuild.model=retention_model(seed,budget)
                    result=rebuild.solve(HERE,tmp,tools,blocked,size,[0],[],[],args.seconds)
                    r=dict(seed=seed,partner_length=size,omissions=budget,result=result)
                    if result["status"]=="witness":
                        p=result["path"];assert len(p)==size+1 and len(set(seed)-set(p))<=budget
                        r["joined"]=checked_join(parent,p);data["best"]=p
                        if len(r["joined"])>=193:write(HERE/"candidate-192.json",r)
                    data["queries"].append(r);write(dest,ledger)
                    print(k[:9],size,budget,result["status"],flush=True)
                    if result["status"]!="witness" or (HERE/"candidate-192.json").is_file():break
    if args.audit:
        out={k:dict(start=len(d["parent"])+len(d["start"])-1,edges=len(d["parent"])+len(d["best"])-1,
             joined=checked_join(d["parent"],d["best"]),replayed_queries=len(d["queries"])) for k,d in ledger.items()}
        write(HERE/"retained-site-replay.json",out)
        print("Strongest retained-site joins",[(k[:9],r["start"],r["edges"]) for k,r in out.items()])

if __name__=="__main__":main()
