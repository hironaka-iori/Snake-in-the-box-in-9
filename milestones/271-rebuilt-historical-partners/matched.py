"""Enumerate opposite arms with one crossing of a specified coordinate inside both Q8 arms."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess, sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
R270=next(MS.glob("270-*"))
sys.path.insert(0,str(R270))
from place_historical import checked, read, write, CSC

def remove_axis(v, bit):
    return (v & (bit-1)) | ((v >> 1) & ~(bit-1))

def insert_axis(v, bit):
    return (v & (bit-1)) | ((v & ~(bit-1)) << 1)

def walk(exe,tmp,blocked,start,threshold,seconds,engine):
    assert start not in blocked
    sites=[0,*sorted(p^start for p in blocked)]
    log=tmp/"paths.csv"
    run=subprocess.run([str(exe),engine,str(threshold),"900000000",str(seconds),str(log)],
            input=",".join(map(str,sites))+"\n0\n",text=True,capture_output=True,check=True)
    status,nodes,count,_,_=run.stdout.split()
    results=[]
    with log.open(encoding="ascii") as f:
        for line in f:
            p=bytes(int(s)^start for s in line.split(","))
            assert p[0]==start and len(p)>=threshold+1 and not set(p)&blocked
            results.append(p)
    assert len(results)==int(count)
    assert status in {"open","complete"}
    return (status=="complete"),results,int(nodes)

def search(exe,tmp,parent,bit,target,seconds,engine):
    jumps=[i for i,(v,w) in enumerate(zip(parent,parent[1:])) if v^w==bit]
    boundary,=jumps
    sides=[[remove_axis(v,bit) for v in part] for part in (parent[:boundary+1],parent[boundary+1:])]
    # Each of the two Q7 segments has at most 50 edges.
    minimum=target-51
    complete,left,visits=walk(exe,tmp,set(sides[0][1:]),0,minimum,seconds,engine)
    groups=defaultdict(list)
    blocked=set(sides[1])
    for p in left:
        if p[-1] not in blocked:groups[p[-1]].append(p)
    left_count=len(left)
    del left
    histogram=Counter()
    best=None
    ports={}
    total_pairs=0
    for port,paths in sorted(groups.items()):
        longest=max(len(p)-1 for p in paths)
        common=set(paths[0][:-1])
        for p in paths[1:]:common.intersection_update(p[:-1])
        done,right,nodes=walk(exe,tmp,blocked|common,port,target-1-longest,seconds,engine)
        complete=complete and done
        visits+=nodes
        ports[port]=dict(left=len(paths),right=len(right),closed=done,common=len(common))
        first=[(a,set(a[:-1])) for a in paths]
        for b in right:
            remaining=set(b)
            for a,occupied in first:
                total_pairs+=1
                edges=len(a)+len(b)-1
                if edges>=target and occupied.isdisjoint(remaining):
                    histogram[edges]+=1
                    if best is None or edges>len(best)-1:
                        best=[insert_axis(v,bit) for v in a]+[insert_axis(v,bit)|bit for v in b]
    return dict(complete=complete,threshold=target,axis=bit.bit_length()-1,first_paths=left_count,
         ports=ports,pairs=total_pairs,histogram=histogram,visits=visits,
         best=checked(parent,best) if best else None)

def main():
    cli=ArgumentParser()
    cli.add_argument("--target",type=int,default=192)
    cli.add_argument("--seconds",type=int,default=6)
    cli.add_argument("--top",type=int,default=8)
    cli.add_argument("--skip",type=int,default=0)
    cli.add_argument("--audit",action="store_true")
    cli.add_argument("--controls",action="store_true")
    opt=cli.parse_args()
    roots=read(R270/"opposite-constructions.json")["roots"]
    selected=[k for k,r in roots.items() if any(n==1 for n in Counter(a^b for a,b in zip(r["parent"],r["parent"][1:])).values())]
    if opt.controls:selected=[k for k in selected if roots[k]["history"]]
    selected.sort(key=lambda k:(not bool(roots[k]["history"]),-roots[k]["best"]["edges"],k))
    dest=HERE/("matched-"+str(opt.target)+("-replay" if opt.audit else "")+".json")
    ledger=read(dest) if dest.exists() else {}
    source=R270/"PrimerPartners.cs"
    with TemporaryDirectory() as folder:
        tmp=Path(folder);exe=tmp/"Q7.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(source)],capture_output=True,check=True)
        for k in selected[opt.skip:opt.skip+opt.top]:
            A=roots[k]["parent"]
            for bit,n in sorted(Counter(a^b for a,b in zip(A,A[1:])).items()):
                if n!=1:continue
                tag=k+":"+str(bit)
                if ledger.get(tag,{}).get("complete"):continue
                row=search(exe,tmp,A,bit,opt.target-len(A),opt.seconds,"array" if opt.audit else "mask")
                row["parent"]=A
                if opt.audit and row["complete"]:
                    original=read(HERE/("matched-"+str(opt.target)+".json"))[tag]
                    if original["complete"]:
                        assert row["first_paths"]==original["first_paths"] and row["pairs"]==original["pairs"]
                        assert {str(a):b for a,b in row["histogram"].items()}==original["histogram"]
                        assert {str(a):b for a,b in row["ports"].items()}==original["ports"]
                ledger[tag]=row
                write(dest,ledger)
                best=row["best"]
                print(tag[:10],row["complete"],row["first_paths"],row["pairs"],best["edges"] if best else None,flush=True)
                if best and best["edges"]>=192:
                    write(HERE/"candidate-192.json",best)
                    return

if __name__=="__main__":
    main()
