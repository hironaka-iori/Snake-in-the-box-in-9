"""Specialize the local table tree to fixed lower occupancy and exact crossing ports."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import json, subprocess, sys
from q9_facet_dual_replay import linear_forests

def export(record,file):
    word=record["word"]; arm=[0]
    for c in word:arm.append(arm[-1]^1<<int(c))
    if "lower_vertices" in record:arm=record["lower_vertices"]
    fixed=set(arm);roots=set(record["ports"]);cert=record["cert"];size=cert["scale"]
    pool=set(range(256))-(fixed-roots);dirs=[sum(1<<i for i in ds) for ds in cert["axes"]]
    price={(m,v,s):p for m,v,s,p in cert["weights"]}
    fees=cert["end_weights"];balance=cert["balance_weight"];required=record["upper_endpoint_counts"]
    base=len(arm)*size+sum(x*y for x,y in zip(fees,required))+balance*record["upper_delta"]
    groups=[];local=defaultdict(set)
    for v in sorted(pool):
        ns=sorted(v^1<<d for d in range(8) if v^1<<d in pool)
        states=[];colour=1-v.bit_count()%2
        for k in range(1<<len(ns)):
            if v not in roots:states.append((k*2,0))
            deg=k.bit_count()+int(v in roots)
            if not (deg==2 or deg==1 and required[colour]>0):continue
            sig=sum(v^u for j,u in enumerate(ns) if k>>j&1)
            score=size-(1-2*(v.bit_count()%2))*balance-int(deg==1)*fees[colour]
            for m in dirs:
                score+=price.get((m,v,sig&m),0);local[m,v].add(sig&m)
            states.append((2*k+1,score))
        groups.append(([v]+ns,states))
    for m in dirs:
        cells=defaultdict(list);axes=[d for d in range(8) if m>>d&1]
        for v in sorted(pool):cells[v&~m].append(v)
        complete=linear_forests(len(axes));fullsize=1<<len(axes)
        for basepoint,cell in cells.items():
            lift=[sum(((v>>d)&1)<<i for i,d in enumerate(axes)) for v in cell]
            pos={v:i for i,v in enumerate(lift)};must=sum(1<<i for i,v in enumerate(cell) if v in roots)
            states=[]
            for k in range(1<<len(cell)):
                if k&must!=must:continue
                big=sum(1<<j for i,j in enumerate(lift) if k>>i&1);codes=complete[big]
                if codes is None:continue
                weight=0
                for code in codes:
                    v=cell[pos[code//fullsize]];sig=sum(1<<d for i,d in enumerate(axes) if (code%fullsize)>>i&1)
                    if sig not in local[m,v]:break
                    weight-=price.get((m,v,sig),0)
                else:states.append((k,weight))
            groups.append((cell,states))
    score=base+sum(max(s for _,s in opts) for _,opts in groups)
    assert score==record["total_scaled"]
    with file.open("w") as f:
        print(base,size,score,len(groups),len(pool),len(fixed),record["majority"],file=f)
        print(*(v+256 for v in sorted(pool)),file=f);print(*sorted(fixed),file=f)
        for scope,opts in groups:
            print(len(scope),len(opts),*(v+256 for v in scope),file=f)
            for k,v in sorted(opts,key=lambda p:-p[1]):print(k,v,file=f)

if __name__=="__main__":
    dest=Path("q9_rigid_ports_trees");dest.mkdir(exist_ok=True)
    for line in Path(sys.argv[1]).read_text().splitlines():
        if not line.endswith("}"):continue
        r=json.loads(line)
        if "total_scaled" not in r:continue
        tag=dest/("d%d_m%d_p%s"%(r["i"],r["majority"],"-".join(map(str,r["ports"]))))
        if tag.with_suffix(".log").exists():continue
        export(r,tag.with_suffix(".tables"))
        rr=subprocess.run(["q9_facet_priced_tree_20261121/tree",str(tag),str(tag.with_suffix(".tree")),"193",sys.argv[2]],capture_output=True,check=True,text=True)
        tag.with_suffix(".log").write_text(rr.stdout);print(tag,rr.stdout.strip(),flush=True)
