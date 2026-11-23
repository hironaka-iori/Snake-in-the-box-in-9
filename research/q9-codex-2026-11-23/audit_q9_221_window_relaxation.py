"""Replay a saved B234 abstract path against the relaxed resources at length 221."""
import argparse
import gzip
import hashlib
import io
import json
import lzma
from pathlib import Path
import sys

import numpy as np


def audit(repo, window_output=None):
    milestone=repo/"milestones/28-combined-identities"
    data=milestone/"data"
    sys.path.insert(0,str(repo/"milestones/25-k7-234"))
    import k7

    source=data/"full_alpha_w3_nogo_path.txt"
    receipt=json.loads((data/"full_alpha_w3_nogo_replay.json").read_text())
    assert hashlib.sha256(source.read_bytes()).hexdigest()==receipt["path_sha256"]
    with gzip.open(repo/"milestones/25-k7-234/data/keys_best234.json.gz","rt") as file:
        keys=json.load(file)["keys"]
    old=[(tuple(x[1]),tuple(x[2])) for x in keys if x[0]=="k6"]
    import resource
    k7.rss_mb=lambda: resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1048576
    graph=k7.K7(object(),old)
    for kind,dirs,syms in keys:
        if kind!="k6":
            graph.add_new((kind,tuple(dirs),tuple(syms)))
    dense=lzma.decompress((data/"k6_dense_W.npy.xz").read_bytes())
    assert hashlib.sha256(dense).hexdigest()==receipt["dense_w_sha256"]
    table=np.load(io.BytesIO(dense)).reshape(-1)
    assert len(table)==graph.nE*k7.NT
    floor={"012031":16,"012304":16,"012314":16,"012345":16,"012032":16,
           "012034":20,"012301":16,"012310":12,"012340":16}
    prefix=receipt["prefix_alpha_floor"]
    a,w,q,bonus=prefix,0,0,0
    pos=receipt["start"]
    lines=source.read_text().splitlines()[1:]
    assert len(lines)==226
    windows=[]
    m=221
    for j,line in enumerate(lines):
        idx,u,_,v,alpha,W=map(int,line.split())
        assert idx==j and pos==u
        x=u%k7.NT*6+(v%6)
        assert v%k7.NT==x%k7.NT and alpha==v%6+1 and W==int(table[v])
        candidates=[graph.X[i] for i,pair in enumerate(graph.XE)
                    if (u//k7.NT,v//k7.NT)==pair and graph.mask(i).ravel()[x]]
        assert candidates
        windows.append(candidates)
        digits=[(x//6**i)%6+1 for i in range(6,-1,-1)]
        assert not any((u==1 and v<4) or (v==1 and u<4) for u,v in zip(digits,digits[1:]))
        assert all(digits[k:k+3]!=[2,2,2] for k in range(5))
        pos=v
        a+=alpha
        w+=W
        directions=tuple(graph.Pr.ext[v//k7.NT][3][-6:])
        word=min(k7.canon(directions),k7.canon(directions[::-1]))
        q+=floor.get("".join(map(str,word)),0)
        bonus+=v//k7.NT in {19,40,74,117,121}
        if j+1==m-8:
            metrics=dict(A=a,W6=w,Q=q,N=bonus)
    assert (a,w)==(receipt["total_alpha_floor"],receipt["total_W6_floor"])
    if window_output is not None:
        window_output.write_text(json.dumps(windows[:m-8])+chr(10))
    A,W6,Q,N=(metrics[x] for x in ("A","W6","Q","N"))
    caps=dict(A=9214-8-35*(m+1),B=100*(221136-840*(m+1)-24*8),W6=373266)
    costs=dict(A=A,B_share=2400*A+20*Q,B_bonus=2400*A+600*N,
               W6_with_max_five_point_correction=W6+12*(m-3))
    assert costs["A"]<caps["A"] and max(costs["B_share"],costs["B_bonus"])<caps["B"]
    assert costs["W6_with_max_five_point_correction"]<caps["W6"]
    return dict(target=m,abstract_edges=m-8,verified_full_path_edges=len(lines),
                metrics=metrics,max_corrected_costs=costs,caps=caps,source_sha256=receipt["path_sha256"])


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("repo",type=Path)
    parser.add_argument("--windows",type=Path)
    a=parser.parse_args()
    print(json.dumps(audit(a.repo,a.windows),indent=2))
