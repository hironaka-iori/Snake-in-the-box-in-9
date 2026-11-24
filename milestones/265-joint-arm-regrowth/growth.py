"""Run the direct constructions and verify every retained pair of arms."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from rank import HERE, MS, bank, load, save, digest

CSC=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")

def seed_pairs():
    placements=load(HERE/"placements.json")["cases"]
    best=sorted(placements,key=lambda k:(-placements[k]["edges"],k))
    starts={k:(placements[k]["A"],placements[k]["B"]) for k in best if placements[k]["edges"]>=172}
    control=load(MS/"259-four-exchange-component/attaining-191.json")
    return {"control":(control["parent"],control["partner"]),**starts}

def checked(A,B):
    if A[0]!=0 or B[0]!=0 or set(A)&set(B)!={0}:raise ValueError("Illegal projected join")
    seq=A[::-1]+[v+256 for v in B]
    return dict(A=A,B=B,joined=seq,edges=len(seq)-1,pairs=bank.check_path(seq,9))

def run():
    parser=ArgumentParser()
    parser.add_argument("--steps",type=int,default=3200)
    parser.add_argument("--copy",type=int,default=0)
    parser.add_argument("--top",type=int,default=100)
    parser.add_argument("--leaders",action="store_true")
    args=parser.parse_args()
    seeds=seed_pairs()
    src=HERE/"JoinedSearch.cs"
    dest=HERE/"growth.json"
    data=load(dest) if dest.exists() else dict(source_sha256=digest(src),placements_sha256=digest(HERE/"placements.json"),runs={})
    if data["source_sha256"]!=digest(src) or data["placements_sha256"]!=digest(HERE/"placements.json"):raise ValueError("Source changed")
    if args.leaders:
        previous=[(k,r) for k,r in data["runs"].items() if r["stage"]=="initial" and r["seed"]!="control"]
        previous.sort(key=lambda entry:-entry[1]["best"]["edges"])
        seeds={}
        seen=set()
        for k,r in previous:
            if r["seed"] in seen:continue
            seen.add(r["seed"])
            seeds[k]=(r["best"]["A"],r["best"]["B"])
    with TemporaryDirectory() as td:
        exe=Path(td)/"Join.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(src)],capture_output=True,check=True)
        for i,(k,(A,B)) in enumerate(list(seeds.items())[:args.top]):
            for mode in (("joint",) if args.leaders or k=="control" else ("joint","fixed")):
                key=f"{k}/{mode}/{args.copy}/{args.steps}"
                if key in data["runs"]:continue
                salt=265000+1000*args.copy+i
                raw=subprocess.run([str(exe),str(salt),str(args.steps),mode],input="\n".join(",".join(map(str,p)) for p in (A,B))+"\n",
                                     check=True,text=True,capture_output=True,timeout=170).stdout.splitlines()
                best=checked(*[list(map(int,l.split(","))) for l in raw[:2]])
                altered=None if raw[2]=="-" else checked(*[list(map(int,l.split(","))) for l in raw[2:4]])
                if best["edges"]<len(A)+len(B)-1 or mode=="fixed" and best["A"]!=A:raise ValueError("Search contract")
                if altered and (altered["A"]==A or altered["B"]==B):raise ValueError("Only one arm changed")
                data["runs"][key]=dict(stage="leaders" if args.leaders else "initial",seed=k,mode=mode,
                    salt=salt,iterations=args.steps,start_edges=len(A)+len(B)-1,best=best,both_changed=altered,
                    counts=dict(zip(("tail_nodes","bridge_nodes","collisions_encountered","repairs","pool_admissions"),map(int,raw[4].split(",")))))
                save(dest,data)
                print(k[:11],mode,len(A)+len(B)-1,best["edges"],(altered or {}).get("edges"),flush=True)
                if best["edges"]>=192:return

if __name__=="__main__":run()
