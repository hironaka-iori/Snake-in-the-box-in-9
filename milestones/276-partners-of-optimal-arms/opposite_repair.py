"""Rebuild an interior interval and the free end of a previously constructed opposite arm."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import os,subprocess
from inputs276 import HERE,read,save
from partners import cases,witness

def main():
    ap=ArgumentParser();ap.add_argument("--gap",type=int,default=12);ap.add_argument("--trim",type=int,default=10)
    ap.add_argument("--target",type=int,nargs="+");a=ap.parse_args();roots=cases()
    out_file=HERE/"placements.json";out=read(out_file) if out_file.exists() else {}
    dest=HERE/"opposite-repairs.json";report=read(dest) if dest.exists() else {}
    with TemporaryDirectory(prefix="q9-opposite276-") as tmp:
        exe=Path(tmp)/"Anchors.exe";csc=Path(os.environ["WINDIR"])/"Microsoft.NET/Framework64/v4.0.30319/csc.exe"
        subprocess.run([str(csc),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"Anchors.cs")],capture_output=True,check=True)
        for k,r in roots.items():
            A=r["parent"];entry=out.setdefault(k,dict(best=witness(A,r["old"]["partner"]),runs=[]))
            source=entry["best"]["partner"];start=entry["best"]["edges"]
            if len(source)<4:continue
            goals=a.target or list(range(min(192,r["old"]["upper"]),start,-1))
            for goal in goals:
                if goal<=entry["best"]["edges"]:continue
                tag="%s-%d-%d-%d-%s"%(k,goal,a.gap,a.trim,bytes(source).hex())
                if tag in report:continue
                branches=[];found=[]
                for order in (0,1):
                    cmd=[str(exe),str(a.gap),str(a.trim),str(order),str(goal-len(A)+1)]
                    feed=k+"\t"+",".join(map(str,source))+"\t"+",".join(map(str,A))+"\n"
                    lines=subprocess.run(cmd,input=feed,text=True,capture_output=True,check=True).stdout.splitlines()
                    parts=[s.split("\t") for s in lines];meta=parts[-1];assert meta[:2]==["S",k]
                    branches.append(dict(setups=int(meta[2]),nodes=int(meta[3]),attained=bool(int(meta[-1]))))
                    for typ,key,line in parts[:-1]:
                        assert typ=="P" and key==k
                        B=list(map(int,line.split(",")));w=witness(A,B);assert w["edges"]==goal
                        found.append(w)
                assert branches[0]["attained"]==branches[1]["attained"]
                report[tag]=dict(root=k,starting_partner=source,target=goal,gap=a.gap,trim=a.trim,orders=branches)
                if found:
                    entry["best"]=found[0];report[tag]["witness"]=found[0]
                    if goal>=192:save(HERE/"candidate-192.json",found[0])
                save(dest,report);save(out_file,out)
                print("Opposite repairs",k[:8],goal,"reached",bool(found),"visited",[w["nodes"] for w in branches],flush=True)
if __name__=="__main__":main()
