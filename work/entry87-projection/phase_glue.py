"""Glue two copies of any 96-edge arc in the published 191-edge bank."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
from solve import BANK,BANK_HASH,sha256,save,defects


def patterns():
    raw=BANK.read_bytes()
    assert sha256(raw).hexdigest()==BANK_HASH
    classes={}
    for seed,row in enumerate(json.loads(raw)):
        path=row["vertex_sequence"]
        step=[(x^y).bit_length()-1 for x,y in zip(path,path[1:])]
        for start in range(len(path)-96):
            block=step[start:start+96]
            keys=[]
            for order in (block,block[::-1]):
                labels={}
                keys.append(tuple(labels.setdefault(b,len(labels)) for b in order))
            key=min(keys)
            classes.setdefault(key,[seed,start,keys[1]<keys[0],0])[3]+=1
    return classes


def examine(exe,start,end):
    classes=list(patterns().items())
    batch=classes[start:end]
    inputs=[]
    for moves,source in batch:
        path=[0]
        for b in moves:path.append(path[-1]^(1<<b))
        assert len(path)==97 and not defects(path)
        inputs.append(path)
    proc=subprocess.run([str(exe)],input="\n".join(" ".join(map(str,p)) for p in inputs),
                        text=True,capture_output=True,check=True)
    lines=iter(proc.stdout.splitlines())
    data=dict(total_classes=len(classes),start=start,end=min(end,len(classes)),classes=[])
    for (moves,src),path in zip(batch,inputs):
        score,copies,*perm=map(int,next(lines).split())
        q=path.copy()
        for b in moves:q.append(q[-1]^(1<<perm[b]))
        failures=defects(q)
        assert len(failures)==score
        row=dict(source=src,minimum_conflicts=score,multiplicity=copies,permutation=perm)
        data["classes"].append(row)
        if score==0:
            tag,*v=next(lines).split()
            assert tag=="witness" and list(map(int,v))==q and len(q)==193
            row["vertices"]=q;break
    assert next(lines,None) is None
    save(Path(f"phase-{start}-{end}.json"),data)
    print(len(classes),len(batch),Counter(r["minimum_conflicts"] for r in data["classes"]),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--from-class",type=int,default=0)
    parser.add_argument("--to-class",type=int,default=200)
    parser.add_argument("--exe",type=Path,default=Path("phase-glue.exe"))
    args=parser.parse_args()
    examine(args.exe.resolve(),args.from_class,args.to_class)
