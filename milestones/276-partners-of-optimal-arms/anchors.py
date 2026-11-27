"""Compare middle-first and tail-first enumeration of all anchored 98-edge repairs."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import os, subprocess
from inputs276 import HERE,read,save,valid,canonical

def run_fixed(keys, src, gap, trim, exe, order):
    lines="".join(k+"\t"+",".join(map(str,src[k]["path"]))+"\n" for k in keys)
    out=subprocess.run([str(exe),str(gap),str(trim),str(order)],input=lines,text=True,
                       capture_output=True,check=True)
    counts={};paths={k:set() for k in keys}
    for line in out.stdout.splitlines():
        z=line.split("\t");k=z[1]
        if z[0]=="S":
            counts[k]=dict(zip(("setups","visited","embeddings","paths"),map(int,z[2:])))
        else:
            assert z[0]=="P"; path=bytes(map(int,z[2].split(",")))
            assert len(path)==99 and path[0]<path[-1] and valid(path,8)==4851
            paths[k].add(path)
    assert all(counts[k]["paths"]==len(paths[k]) for k in keys)
    return counts,paths

def main():
    ap=ArgumentParser();ap.add_argument("--gap",type=int,default=8);ap.add_argument("--trim",type=int,default=4)
    ap.add_argument("--seed-edges",type=int,choices=[97,98]);a=ap.parse_args()
    data=read(HERE/"input-arms.json");src=data["classification"]
    keys=sorted(k for k,r in src.items() if not a.seed_edges or len(r["path"])-1==a.seed_edges)
    name="anchors-%s-g%d-e%d" %(a.seed_edges or "all",a.gap,a.trim)
    dest=HERE/(name+".json");summary=read(dest) if dest.is_file() else dict(gap=a.gap,trim=a.trim,seeds={},shapes={})
    with TemporaryDirectory(prefix="q9-anchors276-") as tmp:
        exe=Path(tmp)/"Anchors.exe";csc=Path(os.environ["WINDIR"])/"Microsoft.NET/Framework64/v4.0.30319/csc.exe"
        subprocess.run([str(csc),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"Anchors.cs")],capture_output=True,check=True)
        for k in keys:
            if k in summary["seeds"]:continue
            first,paths=run_fixed([k],src,a.gap,a.trim,exe,0)
            second,other=run_fixed([k],src,a.gap,a.trim,exe,1)
            assert paths[k]==other[k]
            assert first[k]["setups"]==second[k]["setups"] and first[k]["embeddings"]==second[k]["embeddings"]
            shapes=Counter(canonical(v) for v in paths[k])
            for s in shapes:
                row=summary["shapes"].setdefault(s,dict(path=list(min(v for v in paths[k] if canonical(v)==s)),seeds=[]))
                row["seeds"].append(k)
            summary["seeds"][k]=dict(first=first[k],second=second[k],shapes=shapes,
                labelled_sha256=sha256(b"".join(sorted(paths[k]))).hexdigest())
            save(dest,summary)
            print(name,len(summary["seeds"]),"/",len(keys),"labelled",len(paths[k]),"distinct",len(summary["shapes"]),flush=True)
    summary["complete"]=set(summary["seeds"])==set(keys)
    summary["input_sha256"]=sha256((HERE/"input-arms.json").read_bytes()).hexdigest()
    save(dest,summary)
if __name__=="__main__":main()
