"""Enumerate the second possible signature distance and verify each recovered path."""
import argparse
from itertools import combinations
import json
from math import comb
from pathlib import Path
import subprocess
from solve import BANK,BANK_HASH,defects,save,sha256
from star_repairs import ball,is_path


def connected(triple):
    return sum((v^w).bit_count()<=2 for v,w in combinations(triple,2))>=2


def run(sets,d,target,k,exe):
    data=[f"{d} {target} {k} {len(sets)}"]
    for s in sets:data.append(" ".join(map(str,[len(s),*sorted(s)])))
    proc=subprocess.run([str(exe)],input="\n".join(data),text=True,capture_output=True,check=True)
    rows=[]
    for i,line in enumerate(proc.stdout.splitlines()):
        idx,shapes,*a=map(int,line.split());assert idx==i
        if d==9:assert shapes==384000
        classes,examined,degree,solutions=(a[j:j+3] for j in (0,3,6,9))
        assert classes==[comb(1<<d,z) if z<=k else 0 for z in range(3)]
        u,v,w,y,z,n,*q=a[12:]
        if n:
            s=sets[i]^{u,v,w};assert connected((u,v,w))
            for centre in (y,z):
                if centre>=0:s^=ball(centre,d)
            assert len(q)==n==target and set(q)==s and not defects(q)
        rows.append(dict(shape_count=shapes,classes=classes,examined=examined,degree_models=degree,
                         solutions=solutions,change=[u,v,w,y,z] if n else None,path=q or None))
    assert len(rows)==len(sets)
    return rows


def control(exe):
    triples=[set(t) for t in combinations(range(8),3) if connected(t)]
    sets=[{v for v in range(8) if mask>>v&1} for mask in range(0,256,7)]
    for s,row in zip(sets,run(sets,3,5,2,exe)):
        counts=[0]*3
        for k in range(3):
            for stars in combinations(range(8),k):
                base=s.copy()
                for v in stars:base^=ball(v,3)
                for t in triples:
                    q=base^t
                    if len(q)==5 and is_path(q,3):counts[k]+=1
        assert counts==row["solutions"] and row["shape_count"]==len(triples)
    return len(sets)


if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("first",type=int);parser.add_argument("stop",type=int)
    parser.add_argument("--stars",type=int,choices=(0,1,2),default=2);p=parser.parse_args()
    exe=Path("triple-star.exe").resolve();checks=control(exe);raw=BANK.read_bytes()
    assert sha256(raw).hexdigest()==BANK_HASH
    bank=[set(s["vertex_sequence"]) for s in json.loads(raw)];rows=[]
    # A known 191-edge path with one connected triple and one kernel star applied.
    s=bank[0]^{4,7,8}^ball(117,9)
    assert connected((4,7,8))
    test=run([s],9,192,1,exe)[0];assert test["solutions"][1]
    name=Path(f"triple-star-{p.first}-{p.stop}-{p.stars}.json")
    for start in range(p.first,min(len(bank),p.stop),8):
        chunk=run(bank[start:min(start+8,p.stop)],9,193,p.stars,exe)
        for i,r in enumerate(chunk,start):rows.append(dict(source=i,**r))
        save(name,dict(small_controls=checks,bank_control=test,rows=rows))
        if any(row["path"] for row in chunk):break
    print(len(rows),[sum(r["solutions"][k] for r in rows) for k in range(3)],flush=True)
