"""Reverse each proposed interval and enumerate paths between its two retained ends."""
from collections import Counter
from pathlib import Path
import sys
from intervals import HERE,MS,N,load,save,digest,bank,word

def maximum_gap(seed,parent,i,j):
    outer=set(seed[:i]+seed[j+1:])
    blocked=set(parent[1:])|outer|{w for u in outer for w in N[u]}
    start,end=seed[j],seed[i]
    blocked.discard(start)
    blocked.discard(end)
    visited={start}
    cap=j-i+6
    best=0
    def visit(tip,length):
        nonlocal best
        if length+(tip^end).bit_count()>cap: return
        if tip==end:
            best=max(best,length)
            return
        for u in N[tip]:
            if u in visited or u in blocked or any(v in visited and v!=tip for v in N[u]): continue
            visited.add(u)
            visit(u,length+1)
            visited.remove(u)
    visit(start,0)
    return best

def rooted_word(path):
    axes=[(u^v).bit_length()-1 for u,v in zip(path,path[1:])]
    first=list(dict.fromkeys(axes))
    return bytes(first.index(a) for a in axes)

if __name__=="__main__":
    f=HERE/"intervals.json"
    result=load(f)
    prior=MS/"255-parity-exchange-arms"
    earlier=load(prior/"constructive.json")
    donors=list(load(prior/"partner-pool.json")["shapes"].values())+[r["partner"] for r in earlier["cases"].values()]
    donors += [r["vertices"] for r in earlier["donors"]]
    donors += [r["path"] for group in load(MS/"248-rooted-arm-capacity/attainers.json")["records"] for r in group["paths"]]
    cores={rooted_word(p[i:i+52]) for row in donors for p in (row,row[::-1]) for i in range(len(p)-51)}
    if len(cores)!=2074: raise ValueError("Earlier 51-edge family differs")
    rows={}
    for key,r in result["cases"].items():
        seed,parent=r["seed"],r["rooted_parent"]
        if parent[::-1]+[v+256 for v in r["partner"]]!=r["joined"] or bank.check_path(r["joined"],9)!=r["all_pairs"]["joined"]:
            raise ValueError("Lift differs")
        above=Counter()
        for i in range(len(seed)-2):
            for j in range(i+2,min(i+9,len(seed))):
                length=maximum_gap(seed,parent,i,j)
                if length<j-i: raise ValueError("Original interval lost")
                above[length-(j-i)]+=1
        if max(above)!=r["joined_edges"]-(96+len(seed)): raise ValueError("Bidirectional interval answers disagree")
        rows[key]=dict(intervals=above,outside_old_prefixes=rooted_word(r["partner"][:52]) not in cores,
                       joined_edges=r["joined_edges"],improved=r["joined_edges"]>r["prior_join"])
    save(HERE/"replay.json",dict(input_sha256=digest(f),source_sha256=digest(Path(__file__)),roots=rows,
        checked_intervals=sum(sum(r["intervals"].values()) for r in rows.values()),
        outside_old_prefixes=sum(r["outside_old_prefixes"] for r in rows.values()),
        improved=sum(r["improved"] for r in rows.values()),maximum=max(r["joined_edges"] for r in rows.values())))
