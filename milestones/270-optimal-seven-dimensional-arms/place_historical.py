"""Construct the other Q8 arm for independently obtained long Q8 parents."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json, subprocess, sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"268-archived-94-arms"))
from placement import library,segments,rename,physical,bank,checked,read,write,CSC
from catalogue import label,identifier

def canonical(w):
    return min(rename(w),rename(w[::-1]))

def word(p):
    return canonical(bytes((u^v).bit_length()-1 for u,v in zip(p,p[1:])))

def inputs(data, q7=None):
    fixed={bytes.fromhex(r["canonical"]) for r in data["paths"].values()}
    if q7:
        fixed.update(bytes.fromhex(k) for k in q7)
    cases={}
    for w in sorted(fixed):
        for ordering in (w,w[::-1]):
            p=list(physical(rename(ordering)))
            k=identifier(p)
            cases.setdefault(k,dict(parent=p,shape=w.hex(),history={}))
    for name,digits in data["nine_dimensional"].items():
        # Use integers in the full path, since physical() uses one byte per Q8 vertex.
        whole=[0]
        for d in map(int,digits):whole.append(whole[-1]^(1<<d))
        bank.check_path(whole,9)
        cut=digits.index("8")
        assert digits.count("8")==1 and cut==97
        A,lut=label(whole[:cut+1][::-1])
        B=[lut[(v^whole[cut])&255] for v in whole[cut+1:]]
        k=identifier(A)
        assert cases[k]["parent"]==A
        assert checked(A,B)["edges"]==len(digits)
        cases[k]["history"][name]=B
    return cases,fixed

def run(folder,data,q7=None,iterations=1000,top=10):
    cases,fixed=inputs(data,q7)
    archived=read(MS/"246-eight-dimensional-parents/donors.json")["shapes"]
    pool=set(library()) | fixed | {word(r["path"]) for r in archived}
    pool.update(word(q) for r in cases.values() for q in r["history"].values())
    donors=sorted(pool)
    paths=[list(physical(w)) for w in donors]
    origins=segments(donors,84,98)
    words=sorted(origins)
    images=list(bank.permutation_images())
    target_patterns={length:sorted({w[:length] for w in words if len(w)>=length}) for length in {192-len(r["parent"]) for r in cases.values()}}
    coordinates={length:[physical(w)[:0:-1] for w in ws] for length,ws in target_patterns.items()}
    result={}
    for key,r in cases.items():
        A=r["parent"]
        allowed=bank.allowed_maps(A,images)
        fit=bank.longest(words,allowed)
        witness=bank.make_witness(paths,origins[fit[1]],fit,A)
        b=max([witness["partner"],*r["history"].values()],key=len)
        target=192-len(A)
        # Independent fixed-length scan, using the opposite order of vertex tests.
        hits=0
        for seq in coordinates[target]:
            live=bank.ALL_MAPS
            for v in seq:
                live&=allowed[v]
                if not live:break
            hits+=live.bit_count()
        assert bool(hits)==(witness["joined_edges"]>=192)
        result[key]=dict(**r,placement=witness,target_placements=hits,best=checked(A,b))
        if witness["joined_edges"]>=192:
            write(folder/"candidate-192.json",witness)
    leaders=sorted(cases,key=lambda k:(not bool(cases[k]["history"]),-result[k]["best"]["edges"],k))[:top]
    with TemporaryDirectory() as tmp:
        exe=Path(tmp)/"Grow.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(MS/"265-joint-arm-regrowth/JoinedSearch.cs")],check=True,capture_output=True)
        for i,key in enumerate(leaders):
            r=result[key];a=r["parent"];b=r["best"]["B"]
            seed=270000+i
            raw=subprocess.run([str(exe),str(seed),str(iterations),"fixed"],text=True,capture_output=True,check=True,
                           input="".join(",".join(map(str,p))+"\n" for p in (a,b))).stdout.splitlines()
            p,q=(list(map(int,l.split(","))) for l in raw[:2])
            assert a==p and len(q)>=len(b)
            r["regrowth"]=dict(start_edges=r["best"]["edges"],iterations=iterations,seed=seed)
            r["best"]=checked(p,q)
            if r["best"]["edges"]>=192:write(folder/"candidate-192.json",r["best"])
    for r in result.values():
        q=r["best"]["joined"]
        occupied=set(q)
        assert len(occupied)==len(q) and all(0<=v<512 for v in q)
        for i,u in enumerate(q):
            assert {u^(1<<j) for j in range(9)}&occupied==set(q[max(0,i-1):i]+q[i+1:i+2])
    out=dict(roots=result,donors=len(pool),words=len(words),fixed_shapes=len(fixed),target_words={n:len(ws) for n,ws in target_patterns.items()},
             best=max(r["best"]["edges"] for r in result.values()),best_placements=max(r["placement"]["joined_edges"] for r in result.values()),
             successful_target_placements=sum(r["target_placements"] for r in result.values()))
    write(folder/"opposite-constructions.json",out)
    print({k:v for k,v in out.items() if k!="roots"},flush=True)

if __name__=="__main__":
    cli=ArgumentParser()
    cli.add_argument("--all-primers",action="store_true")
    cli.add_argument("--iterations",type=int,default=4000)
    cli.add_argument("--top",type=int,default=20)
    opt=cli.parse_args()
    q7=read(HERE/"q8-primer-arms.json") if opt.all_primers else None
    run(HERE,read(HERE/"uga270.json"),q7,opt.iterations,opt.top)
