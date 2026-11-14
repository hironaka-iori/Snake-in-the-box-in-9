"""Independent all-pair checks and small-cube census for the closed-star search."""
import argparse
from itertools import combinations
import json
from math import comb
from pathlib import Path
import subprocess
from solve import BANK, BANK_HASH, defects, save, sha256


def ball(v,d):
    return {v}|{v^(1<<j) for j in range(d)}


def decide(sets,d,target,k,exe):
    stream=[f"{d} {target} {k} {len(sets)}"]
    for s in sets:stream.append(" ".join(map(str,[len(s),*sorted(s)])))
    process=subprocess.run([str(exe)],input="\n".join(stream),text=True,capture_output=True,check=True)
    rows=[]
    for i,line in enumerate(process.stdout.splitlines()):
        idx,*data=map(int,line.split());assert i==idx
        classes,examined,degree,hits=(data[j:j+3] for j in (0,3,6,9))
        assert classes==[comb(1<<d,j) if j<=k else 0 for j in range(3)]
        v,a,b,n,*q=data[12:];assert len(q)==n
        if q:
            s=sets[i]^{v}
            for centre in (a,b):
                if centre>=0:s^=ball(centre,d)
            assert s==set(q) and len(q)==target and not defects(q)
        rows.append(dict(source=i,classes=classes,examined=examined,degree_models=degree,
                         solutions=hits,change=[v,a,b] if q else None,path=q or None))
    assert len(rows)==len(sets)
    return rows


def is_path(s,d):
    graph={v:(ball(v,d)-{v})&s for v in s}
    tips=[v for v,ns in graph.items() if len(ns)==1]
    if len(tips)!=2 or any(len(ns) not in (1,2) for ns in graph.values()):return False
    seen=set();todo=[tips[0]]
    while todo:
        v=todo.pop()
        if v not in seen:seen.add(v);todo.extend(graph[v]-seen)
    return seen==s


def control(exe):
    # Direct census, including every v even when the native first-bad-site filter would prune it.
    sets=[{v for v in range(8) if mask>>v&1} for mask in range(256)]
    rows=decide(sets,3,5,2,exe)
    for s,r in zip(sets,rows):
        counts=[0]*3
        for k in range(3):
            for stars in combinations(range(8),k):
                u=s.copy()
                for a in stars:u^=ball(a,3)
                for v in range(8):
                    y=u^{v}
                    if len(y)==5 and is_path(y,3):counts[k]+=1
        assert counts==r["solutions"]
    return len(sets)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--exe",type=Path,default=Path("star-repairs.exe"))
    a=p.parse_args();exe=a.exe.resolve();n=control(exe)
    data=BANK.read_bytes();assert sha256(data).hexdigest()==BANK_HASH
    sets=[set(r["vertex_sequence"]) for r in json.loads(data)]
    # A constructed nine-cube test forces an available correction with two kernel stars.
    goal=sets[0];base=goal^{135}^ball(28,9)^ball(330,9)
    positive=decide([base],9,192,2,exe)[0];assert positive["solutions"][2] and positive["path"]
    rows=decide(sets,9,193,2,exe)
    save(Path("closed-star-repairs.json"),dict(exhaustive_Q3_controls=n,Q9_control=positive,sources=rows))
    print(len(rows),[sum(row["solutions"][k] for row in rows) for k in range(3)],flush=True)
