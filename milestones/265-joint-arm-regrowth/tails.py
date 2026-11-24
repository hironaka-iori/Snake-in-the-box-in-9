"""Seek 192 by regrowing both sides of a central segment of each one-crossing 191-edge bank path."""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from growth import HERE,MS,bank,load,save,digest,checked,CSC

BANK=MS.parent/"work/bank9.json"

def bank_pairs():
    rows=[]
    for index,entry in enumerate(load(BANK)):
        p=entry["vertex_sequence"]
        if len(p)!=192:continue
        steps=[u^v for u,v in zip(p,p[1:])]
        for axis in range(9):
            bit=1<<axis
            if steps.count(bit)!=1:continue
            cut=steps.index(bit)
            def project(seq):
                anchor=seq[0]
                return [((v^anchor)&(bit-1))|(((v^anchor)>>(axis+1))<<axis) for v in seq]
            A=project(p[:cut+1][::-1]);B=project(p[cut+1:])
            if len(B)>len(A):A,B=B,A
            assert checked(A,B)["edges"]==191
            rows.append((index,axis,A,B))
    return rows

def canonical(a,b):
    moves=[u^v for p in (a,b) for u,v in zip(p,p[1:])]
    axes=list(dict.fromkeys(moves))
    return bytes(axes.index(d) for d in moves)

def groups(width):
    out={}
    for i,j,a,b in bank_pairs():
        A,B=a[:width+1],b[:width+1]
        if canonical(A,B)>canonical(B,A):A,B=B,A
        key=canonical(A,B).hex()
        row=out.setdefault(key,dict(A=A,B=B,bank_crossings=[]))
        row["bank_crossings"].append([i,j])
    return out

def main():
    args=ArgumentParser()
    args.add_argument("widths",type=int,nargs="+")
    args.add_argument("--nodes",type=int,default=200000)
    cfg=args.parse_args()
    src=HERE/"TailPairs.cs";dest=HERE/"tail-pairs.json"
    data=load(dest) if dest.exists() else dict(source_sha256=digest(src),bank_sha256=digest(BANK),widths={})
    if (data["source_sha256"],data["bank_sha256"])!=(digest(src),digest(BANK)):raise ValueError("Source changed")
    with TemporaryDirectory() as tmp:
        exe=Path(tmp)/"Pairs.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(src)],check=True,capture_output=True)
        for width in cfg.widths:
            records=data["widths"].setdefault(str(width),{})
            for key,base in groups(width).items():
                prior=records.get(key)
                if prior and (prior["status"]!="open" or prior["node_limit"]>=cfg.nodes):continue
                lines=subprocess.run([str(exe),"192",str(cfg.nodes)],input="".join(",".join(map(str,base[q]))+"\n" for q in ("A","B")),
                    text=True,capture_output=True,check=True,timeout=150).stdout.strip().splitlines()
                trees=[]
                for line in lines[1:3]:
                    n,c,full,lengths=line.split()
                    trees.append(dict(nodes=int(n),reachable_prunes=int(c),complete=bool(int(full)),length_counts=list(map(int,lengths.split(",")))))
                record=dict(**base,status=lines[0],trees=trees,node_limit=cfg.nodes,pairs=int(lines[3]))
                if lines[0]=="witness":
                    a,b=(list(map(int,s.split(","))) for s in lines[4:6])
                    assert a[:width+1]==base["A"] and b[:width+1]==base["B"]
                    record["witness"]=checked(a,b)
                records[key]=record
                save(dest,data)
                if lines[0]=="witness":print("192-edge witness",width,key,flush=True);return
            print(width,Counter(r["status"] for r in records.values()),flush=True)
if __name__=="__main__":main()
