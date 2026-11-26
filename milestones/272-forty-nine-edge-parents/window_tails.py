"""Exhaust all two-ended extensions to 49 edges for every specified Q7 interval."""
from argparse import ArgumentParser
from collections import Counter
from tempfile import TemporaryDirectory
from pathlib import Path
import subprocess
from parents import HERE,R270,read,write,points,paircheck,unrooted
from primer_census import CSC

def main():
    ap=ArgumentParser();ap.add_argument("--window",type=int,default=24);ap.add_argument("--reverse",action="store_true");opt=ap.parse_args()
    n=opt.window
    parents=read(R270/"palani-q7.json")["paths"]
    windows={unrooted(r["q7_parent"][i:i+n+1]) for r in parents.values() for i in range(51-n)}
    all_shapes=set()
    entries={}
    with TemporaryDirectory() as tmp:
        exe=Path(tmp)/"Windows.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"WindowTails.cs")],check=True,capture_output=True)
        for k in sorted(windows):
            p=points(bytes.fromhex(k)[::-1 if opt.reverse else 1])
            raw=subprocess.run([str(exe)],input=",".join(map(str,p))+"\n",text=True,capture_output=True,check=True)
            lines=raw.stdout.splitlines();tag,nodes,c=lines.pop().split()
            assert tag=="T" and len(lines)==int(c)
            found=Counter()
            for line in lines:
                assert line.startswith("P ")
                path=list(map(int,line[2:].split(",")))
                assert len(path)==50 and any(path[i:i+len(p)]==p for i in range(51-len(p)))
                paircheck(path,7);found[unrooted(path)]+=1
            entries[k]=dict(nodes=int(nodes),occurrences=found)
            all_shapes.update(found)
    data=dict(window=n,windows=entries,parents=sorted(all_shapes))
    orig=HERE/("parents-wide-"+str(n)+".json")
    if opt.reverse:
        initial=read(orig)
        assert initial["parents"]==data["parents"]
        for k,row in entries.items():assert initial["windows"][k]["occurrences"]==row["occurrences"]
    write(HERE/("parents-wide-"+str(n)+("-replay" if opt.reverse else "")+".json"),data)
    print(n,len(entries),len(all_shapes),sum(v["nodes"] for v in entries.values()),flush=True)

if __name__=="__main__":main()
