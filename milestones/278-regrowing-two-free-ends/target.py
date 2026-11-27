"""Search for length 192 with a retained central interval and both free ends unrestricted in Q9."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from archive import HERE,cases,code,write,read
from grow import independent_check

def run(args):
    data,bank,info=cases(args.width,args.minimum,True)
    tag="target-%d-%d-%d"%(args.minimum,args.width,args.target)
    solve_data(args,data,tag)

def solve_data(args,data,tag):
    archive=read(tag+".json") if (HERE/(tag+".json")).exists() else {}
    with TemporaryDirectory(prefix="q9-target-") as d:
        tmp=Path(d)
        for engine,name in [("Target","degree-and-leaves"),("TargetReplay","reversed-components")]:
            if args.engine and args.engine!=engine:continue
            source=HERE/(engine+".cs"); exe=tmp/(engine+".exe")
            subprocess.run(["C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe","/nologo","/optimize+","/out:"+str(exe),str(source)],check=True)
            lines=[];rows={}
            for key,r in sorted(data.items()):
                k=sha256(key).hexdigest()
                if k not in archive:
                    archive[k]=dict(source=r["source"],occurrences=r["occurrences"],retained_edges=len(key),records={},**({"offset":r["offset"]} if "offset" in r else {}))
                old=archive[k]["records"].get(name,{})
                if old.get("budget",0)>=args.budget or old.get("status") in {"witness","excluded"}:continue
                if args.only and not k.startswith(args.only):continue
                core=r["a"]+r["m"]+r["b"];independent_check(core);rows[k]=core
                lines.append(k+"\t"+",".join(map(str,core)))
            if not lines:continue
            src=tmp/"in";res=tmp/"out"
            src.write_text("\n".join(lines)+"\n",encoding="ascii")
            subprocess.run([str(exe),str(src),str(res),str(args.target),str(args.budget)],check=True)
            for line in res.read_text().splitlines():
                k,state,n,p,chain=line.split("\t")
                row=dict(status=state,nodes=int(n),pruned=int(p),budget=args.budget,source_sha256=sha256(source.read_bytes()).hexdigest())
                if state=="witness":
                    seq=list(map(int,chain.split(",")));independent_check(seq);assert len(seq)==args.target+1
                    core=rows[k]
                    assert any(seq[i:i+len(core)] in (core,core[::-1]) for i in range(len(seq)-len(core)+1))
                    row["path"]=seq
                    if args.target>=192:write("candidate-192.json",row)
                old=archive[k]["records"];old[name]=row
                assert len({x["status"] for x in old.values()}&{"witness","excluded"})<=1
            write(tag+".json",archive)
            print(engine,Counter(r["records"][name]["status"] for r in archive.values() if name in r["records"]),flush=True)
            if (HERE/"candidate-192.json").exists():return
    pairs=[r for r in archive.values() if len(r["records"])==2 and all(x["status"]=="excluded" for x in r["records"].values())]
    print("Two exclusions",len(pairs),"of",len(data),"original paths",sum(r["occurrences"] for r in pairs))
if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("width",type=int);ap.add_argument("--minimum",type=int,default=191)
    ap.add_argument("--target",type=int,default=192);ap.add_argument("--budget",type=int,default=100000)
    ap.add_argument("--engine",choices=["Target","TargetReplay"]);ap.add_argument("--only")
    run(ap.parse_args())



