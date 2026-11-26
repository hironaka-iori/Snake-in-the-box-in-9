"""Use the Round 271 unrestricted solver and independent formula replay for these parents."""
from argparse import ArgumentParser
from itertools import permutations
from hashlib import sha256
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
R271=MS/"271-rebuilt-historical-partners"
sys.path.insert(0,str(R271))
# Round 271 imports the Round 269 module named opposite. Load it before the
# current directory can match that module name when this script is executed.
sys.path.insert(0,str(MS/"269-archived-93-arms"))
import hunt
import transport271
from hunt import bank,pack,read,write

old_catalogue=transport271.catalogue

def catalogue(ms):
    refs,pins=old_catalogue(ms)
    for parents_file,summary_file in [("270-optimal-seven-dimensional-arms/opposite-constructions.json",
                                      "271-rebuilt-historical-partners/summary.json")]:
        parents=read(ms/parents_file)["roots"]
        bounds=read(ms/summary_file)["roots"]
        for f in (parents_file,summary_file):pins[f]=sha256((ms/f).read_bytes()).hexdigest()
        for k,r in bounds.items():
            p=parents[k]["parent"];length=r["maximum"]-len(p)+1
            refs["271/"+k]=(tuple(sorted(p[1:])),length)
    return refs,pins

def cases():
    return read(HERE/"opposite-constructions.json")["roots"]

def plan():
    roots=cases();images=list(bank.permutation_images())
    transfers=transport271.build_transfers(HERE,MS,roots,images)
    groups=[]
    for n in sorted({len(r["parent"])-1 for r in roots.values()},reverse=True):
        ordered=sorted((row["shape"],k,row["parent"]) for k,row in roots.items() if len(row["parent"])==n+1)
        for start in range(0,len(ordered),96):
            chunk={k:p for _,k,p in ordered[start:start+96]}
            for group in pack(chunk,images,n-6):
                group["length"]=n
                groups.append(group)
    def key(g):
        ids=g["ranks"];active=[k for k in ids if transfers.get(k,{}).get("ceiling",999)>=192]
        return (not bool(active),-g["length"],min(roots[k]["repair_start"]["needed_new_sites"] for k in ids),
                -max(roots[k]["best"]["edges"] for k in ids),-len(ids),min(ids))
    groups.sort(key=key);write(HERE/"groups.json",groups)
    print("Groups",len(groups),"for",len(roots),"roots",flush=True)

def main():
    cli=ArgumentParser()
    cli.add_argument("action",choices=["plan","search","audit"])
    cli.add_argument("--target",type=int,default=192)
    cli.add_argument("--parents",type=int,nargs="+",default=[96,97,98])
    cli.add_argument("--seconds",type=float,default=3)
    cli.add_argument("--depth",type=int,default=0)
    cli.add_argument("--only",type=int,nargs="+")
    cli.add_argument("--deficit",action="store_true")
    cli.add_argument("--improve-only",action="store_true")
    args=cli.parse_args();args.controls=False
    transport271.catalogue=catalogue
    hunt.HERE=HERE;hunt.R270=HERE;hunt.cases=cases
    if args.action=="plan":plan()
    elif args.action=="search":hunt.proof_search(args)
    else:
        hunt.audit()
        best=read(HERE/"best-join.json")
        if best["source"]=="Round 270":
            best["source"]="Round 273 donor placement or regrowth"
            write(HERE/"best-join.json",best)

if __name__=="__main__":main()
