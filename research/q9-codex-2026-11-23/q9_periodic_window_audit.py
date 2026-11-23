"""Test whether a verified coil survives long-window and budget relaxations."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from q9_geometry_count_edits import encode
from q9_window_geometry import canonical
from q9_window_geometry_dp import read_graph


def audit(cycle,graph,table,k7):
    n=len(cycle)
    assert n==len(set(cycle))==192
    assert all(((v^w).bit_count()==1)==(i-j in (1,n-1))
               for i,v in enumerate(cycle) for j,w in enumerate(cycle[:i]))
    select=set(cycle)
    axes=[(v^cycle[(i+1)%n]).bit_length()-1 for i,v in enumerate(cycle)]
    a=[]
    for i,v in enumerate(cycle):
        p,q=axes[i-1],axes[i]
        a.append(sum((v^(1<<j)^(1<<k)) not in select for j,k in combinations(range(9),2)
                     if j not in (p,q) and k not in (p,q)))
    clamped=[min(6,x) for x in a]
    assert all(x>=1 for x in clamped)
    arc_data=[]
    for start in range(n):
        words=[axes[(start+i)%n] for i in range(221)]
        alpha=[clamped[(start+i)%n] for i in range(1,221)]
        actual=[a[(start+i)%n] for i in range(1,221)]
        bad=0
        W=0
        for k in range(213):
            arc=graph.xid[canonical(words[k:k+9])]
            source,target=graph.XE[arc]
            code=encode(alpha[k+1:k+8])
            i,j=code//6,code%k7.NT
            bad+=not (graph.alive[source,i] and graph.alive[target,j] and not graph.newcnt[arc,code])
            W+=int(table[target*k7.NT+j])
        uses=Counter(words)
        freq=sorted(uses[d] for d in range(9))
        arc_data.append(dict(start=start,alpha=sum(alpha),true_alpha=sum(actual),W6=W,
                             excluded_windows=bad,least_two=sum(freq[:2]),directions=freq))
    best=min(arc_data,key=lambda x:(x["excluded_windows"],x["W6"]))
    return dict(coil_edges=n,all_windows_up_to=n-2,rotations=n,best=best,
                min_A=min(r["alpha"] for r in arc_data),max_A=max(r["alpha"] for r in arc_data),
                min_excluded=min(r["excluded_windows"] for r in arc_data),
                rotations_below_all_caps=sum(r["alpha"]<=1436 and
                    2400*r["alpha"]+600*213<=3446400 and r["W6"]+2616<=373266 and
                    not r["excluded_windows"] for r in arc_data),
                max_least_two=max(r["least_two"] for r in arc_data))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repo",type=Path)
    p.add_argument("coil",type=Path)
    a=p.parse_args()
    k7,graph,table,_,_=read_graph(a.repo)
    print(json.dumps(audit(json.loads(a.coil.read_text())["cycle"],graph,table,k7),indent=2))
