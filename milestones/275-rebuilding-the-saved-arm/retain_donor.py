"""Seek an extra opposite-face edge while retaining the sites of the 189-edge donor."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from rebuild_saved import HERE,MS,MAIN,face,resolve,read,save,make_witness

def main():
    ap=ArgumentParser()
    ap.add_argument("--roots",nargs="+",default=[MAIN])
    ap.add_argument("--target",type=int,default=190)
    ap.add_argument("--budgets",type=int,nargs="+",default=[6,10,16,24])
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--audit",action="store_true");opt=ap.parse_args()
    hunt=face.dependencies(MS)
    from retain import retention_model, checked_join
    src=read(HERE/"saved-placements.json")["roots"]
    dest=HERE/"retained.json";ledger=read(dest) if dest.exists() else {}
    roots=list(ledger) if opt.audit else [resolve(src,x) for x in opt.roots]
    found={};counts={}
    with TemporaryDirectory(prefix="q9-r275-retain-") as td:
        tmp=Path(td);tools=hunt.rebuild.masks.compilers(tmp)
        for k in roots:
            w=src[k]["best"];p=w["A"];seed=w["B"];blocked=set(p[1:])
            rows=ledger.setdefault(k,{})
            if opt.audit:
                for key,row in rows.items():
                    n=row["target"]-len(p);omits=row["omissions"];res=row["result"]
                    assert key==f"{row['target']}/{omits}" and row["donor"]==seed
                    cnf,sel=hunt.deficit.model(blocked,n,[0],res["cycles"],[])
                    cnf.at_most([-sel[v] for v in sorted(set(seed)-{0})],omits)
                    f=tmp/"independent.cnf";assert cnf.save(f)==res["cnf"] and len(cnf.clauses)==res["clauses"]
                    stat=res["status"];counts[stat]=counts.get(stat,0)+1
                    if stat=="excluded":
                        proof=HERE/res["proof"]
                        assert sha256(proof.read_bytes()).hexdigest()==res["compressed"]
                        assert hunt.rebuild.masks.p.check_proof(f,proof,tools[0])==res["replay"]
                    elif stat=="witness":
                        b=res["path"];q=checked_join(p,b)
                        assert len(set(seed)-set(b))<=omits and len(q)-1==row["target"] and q==row["joined"]
                        if k not in found or found[k]["edges"]<row["target"]:found[k]=make_witness(p,q)
                continue
            n=opt.target-len(p)
            for budget in sorted(opt.budgets):
                tag=f"{opt.target}/{budget}"
                if any(r["target"]==opt.target and r["result"]["status"]=="witness" for r in rows.values()):break
                if any(r["target"]==opt.target and r["omissions"]>=budget and r["result"]["status"]=="excluded" for r in rows.values()):continue
                old=rows.get(tag,{}).get("result",{})
                hunt.rebuild.model=retention_model(seed,budget)
                res=hunt.rebuild.solve(HERE,tmp,tools,blocked,n,[0],old.get("cycles",[]),[],opt.seconds)
                row=dict(target=opt.target,omissions=budget,donor=seed,result=res)
                if res["status"]=="witness":
                    row["joined"]=checked_join(p,res["path"])
                    assert len(row["joined"])==opt.target+1 and len(set(seed)-set(res["path"]))<=budget
                    if opt.target>=192:save(HERE/"candidate-192.json",row)
                rows[tag]=row;save(dest,ledger)
                print(k[:10],opt.target,budget,res["status"],flush=True)
    if opt.audit:
        save(HERE/"retained-replay.json",dict(best=found,checked=counts))
        print("Retained-site replay",counts,flush=True)
if __name__=="__main__":main()
