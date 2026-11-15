"""Trim an odd number of terminal sites and replace the whole middle between its old roots."""
import argparse,json
from collections import Counter
from itertools import permutations
from pathlib import Path
from free_last_drat import decide
from solve import BANK,BANK_HASH,sha256,defects,save
from punctured_lift import project


def canonical(A,B):
    answers=[]
    for a,b in ((A,B),(B,A)):
        names={}
        for q in (a,b):
            for x,y in zip(q,q[1:]):
                i=(x^y).bit_length()-1;names.setdefault(i,len(names))
        unused=sorted(set(range(8))-names.keys())
        for tail in permutations(unused):
            labels={**names,**{x:len(names)+j for j,x in enumerate(tail)}}
            def normal(x):return sum(((x^a[0])>>i&1)<<j for i,j in labels.items())
            answers.append((tuple(map(normal,a)),tuple(map(normal,b))))
    return min(answers)


def menu():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw);registry={};sources=set()
    for i,entry in enumerate(bank):
        path=entry["vertex_sequence"]
        for axis in range(9):
            trace,sw=project(path,axis)
            if len(sw)!=2:continue
            sources.add(i);u,v=sw
            A=trace[:u+1][::-1];B=trace[v:];M=trace[u:v+1]
            assert len(A)+len(B)+len(M)==192 and not defects(A[::-1]+[x|256 for x in M]+B)
            for trim in range(1,99-len(M),2):
                for left in range(trim+1):
                    right=trim-left
                    if left>=len(A) or right>=len(B):continue
                    a=A[:len(A)-left];b=B[:len(B)-right]
                    key=canonical(a,b)
                    if key not in registry:
                        ca,cb=key
                        registry[key]=dict(first=ca,last=cb,target=193-len(ca)-len(cb),sources=[])
                    r=registry[key];assert r["target"]==len(M)+trim+1
                    r["sources"].append([i,axis,left,right])
    assert len(sources)==88
    return list(registry.values())


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=250000);z=p.parse_args()
    file=Path("replaced-middle-menu.json")
    if file.exists():cases=json.loads(file.read_bytes())
    else:cases=menu();save(file,cases)
    rows=[];dest=Path(f"replaced-middles-{z.first}-{z.stop}-{z.budget}.json")
    for i in range(z.first,min(z.stop,len(cases))):
        r=cases[i];a,b=map(list,(r["first"],r["last"]));assert a[0]==0
        allowed=(set(range(256))-(set(a)|set(b)))|{a[0],b[0]}
        result=decide(allowed,r["target"],z.budget,f"middle-change-{i}",None,b[0],8)
        q=result.get("path")
        if q:
            full=a[::-1]+[x|256 for x in q]+b
            assert len(full)==193 and not defects(full);result["vertices"]=full
        rows.append(dict(index=i,**result));save(dest,rows)
        if q:break
    print(len(cases),len(rows),Counter(r["status"] for r in rows),flush=True)
