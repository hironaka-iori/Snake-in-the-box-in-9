"""Exact extension census of the long arms retaining one reference segment."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
LAST=BASE/"251-eighty-edge-segments"
sys.path.insert(0,str(BASE/"250-corner-partners"))
import core_audit as audit

COMPILER=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def read(path):
    return json.loads(path.read_bytes())


def shape_id(path):
    return sha256(audit.key(path)).hexdigest()


def references():
    paths={str(r["donor_index"]):r["path"] for r in read(audit.INVENTORY)["rows"]}
    paths.update({r["id"]:r["path"] for r in read(audit.GEOMETRY)["corner_closure"]["new_shapes"]})
    if len({shape_id(p) for p in paths.values()})!=22:
        raise ValueError("Changed reference collection")
    return paths


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--core",type=int,required=True,choices=range(55,72))
    args=cli.parse_args()
    k=args.core
    refs=references()
    previous=read(LAST/"census-72.json")
    inherited=set(previous["inherited_ids"])|{r["id"] for r in previous["new_shapes"]}
    if len(inherited)!=28: raise ValueError("Unexpected inherited catalogue")
    windows={}
    for label,p in refs.items():
        audit.verify_path(p)
        for start in range(len(p)-k):
            q=p[start:start+k+1]
            windows.setdefault(audit.key(q),(label,start,q))
    cores=list(windows.values())
    records={}
    counts={}
    with TemporaryDirectory(prefix="snake252-grow-") as name:
        temp=Path(name); exe=temp/"Grow.exe"; inp=temp/"segments"; out=temp/"output"
        subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"Grow.cs")],check=True)
        inp.write_text("".join(",".join(map(str,q))+"\n" for _,_,q in cores),encoding="ascii")
        subprocess.run([str(exe),str(inp),str(out)],check=True)
        with out.open() as result:
            for line in result:
                kind,index,payload=line.strip().split(" ",2)
                i=int(index)
                if kind=="C":
                    if i in counts: raise ValueError("Repeated segment")
                    counts[i]=int(payload)
                    continue
                left,word=payload.split()
                p=list(map(int,word.split(",")))
                left=int(left); label,start,q=cores[i]
                if kind!="P" or not 96<=len(p)-1<=98 or p[left:left+k+1]!=q:
                    raise ValueError("Completion does not contain the recorded core")
                key=shape_id(p)
                if key not in records:
                    audit.verify_path(p)
                    records[key]=dict(id=key,edges=len(p)-1,path=p,donor=label,start=start,left=left)
    if set(counts)!=set(range(len(cores))) or not inherited<=records.keys():
        raise ValueError("Incomplete segment or inherited shape coverage")
    new=[r for key,r in records.items() if key not in inherited]
    for r in new:r["longest_reference_segment"]=k
    for width in range(k+1,73):
        keys={audit.key(p[i:i+width+1]) for p in refs.values() for i in range(len(p)-width)}
        for r in new:
            p=r["path"]
            if r["longest_reference_segment"]==width-1 and any(audit.key(p[i:i+width+1]) in keys for i in range(len(p)-width)):
                r["longest_reference_segment"]=width
    if any(r["longest_reference_segment"]==72 for r in new):raise ValueError("Older census missed a shape")
    new.sort(key=lambda r:(-r["edges"],-r["longest_reference_segment"],r["id"]))
    files=[Path(__file__),HERE/"Grow.cs",LAST/"census-72.json",audit.INVENTORY,audit.GEOMETRY,Path(audit.__file__)]
    data=dict(core=k,source_hashes={p.relative_to(BASE.parent).as_posix():audit.digest(p) for p in files},
              compiler_sha256=audit.digest(COMPILER),occurrences=sum(len(p)-k for p in refs.values()),
              segment_classes=len(cores),nodes=sum(counts.values()),total_classes=len(records),
              lengths=Counter(r["edges"] for r in records.values()),all_ids=sorted(records),new_shapes=new,
              segments=[dict(donor=label,start=start,nodes=counts[i]) for i,(label,start,q) in enumerate(cores)])
    (HERE/f"census-{k}.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(k,data["occurrences"],len(cores),data["nodes"],len(records),dict(data["lengths"]),len(new),flush=True)


if __name__=="__main__":main()
