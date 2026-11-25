"""Determine how many old opposite-arm sites must be lost to grow the 187-edge join by one edge."""
from argparse import ArgumentParser
from tempfile import TemporaryDirectory
from retain import HERE,Path,read,write,checked_join,retention_model,rebuild

def main():
    ap=ArgumentParser();ap.add_argument("--seconds",type=float,default=15)
    a=ap.parse_args()
    dest=HERE/"retained-sites.json";ledger=read(dest)
    k,r=next((k,r) for k,r in ledger.items() if len(r["parent"])==97 and len(r["start"])==91)
    seed=r["start"];parent=r["parent"];n=len(seed);blocked=set(parent[1:])
    with TemporaryDirectory() as d:
        tmp=Path(d);tools=rebuild.masks.compilers(tmp)
        while True:
            queries=[q for q in r["queries"] if q["seed"]==seed and q["partner_length"]==n]
            low=max(q["omissions"] for q in queries if q["result"]["status"]=="excluded")+1
            upper=min(len(set(seed)-set(q["result"]["path"])) for q in queries if q["result"]["status"]=="witness")
            assert low<=upper
            if low==upper:break
            budget=(low+upper-1)//2
            if any(q["omissions"]==budget and q["result"]["status"]=="open" for q in queries):
                possible=[b for b in range(low,upper) if all(q["omissions"]!=b for q in queries)]
                if not possible:break
                budget=possible[-1]
            rebuild.model=retention_model(seed,budget)
            result=rebuild.solve(HERE,tmp,tools,blocked,n,[0],[],[],a.seconds)
            row=dict(seed=seed,partner_length=n,omissions=budget,result=result)
            if result["status"]=="witness":
                arm=result["path"];assert len(arm)==n+1 and len(set(seed)-set(arm))<=budget
                row["joined"]=checked_join(parent,arm)
            r["queries"].append(row);write(dest,ledger)
            print(budget,result["status"],flush=True)
    write(HERE/"minimum-omissions.json",dict(root=k,seed=seed,minimum=low,maximum=upper,
          retained_parent=parent,old_partner_length=n-1,requested_partner_length=n))
    print("Minimum omissions",low,upper)
if __name__=="__main__":main()
