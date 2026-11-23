"""Check face-inequality weights directly and reconcile all parent/endpoint searches."""
from itertools import combinations
import json,gzip
from pathlib import Path
from collections import Counter
from verify_q9_center_avoidance import verify,forms
from verify_q8_free_layer_dual import is_forest
from concurrent.futures import ProcessPoolExecutor
def check(record):
    p=record["parent"];verify(p);level=record["threshold"];ep=record["end_colour"]
    assert len(p)==192 and level in (1,2,3) and ep in (0,1)
    old=set(p);domain={v for v in range(512) if v in old or sum(v^1<<j in old for j in range(9))<=level}
    scale=record["scale"];fee=record["end"];mu=record["balance"];assert type(scale)is int and scale>0
    dual={(m,v,z):n for m,v,z,n in record["weights"]};assert len(dual)==len(record["weights"])
    axes=[tuple(1<<j for j in grp) for grp in record["axes"]]
    masks=[sum(x) for x in axes]
    total=2*fee+(1-2*ep)*mu
    sig={}
    for v in domain:
        nbr=[1<<j for j in range(9) if v^1<<j in domain]
        patterns=[a|b for a,b in combinations(nbr,2)]
        if v.bit_count()%2==ep:patterns+=nbr
        scores=[0]
        for z in patterns:
            score=scale-(1-2*(v.bit_count()%2))*mu-int(z.bit_count()==1)*fee
            scores.append(score+sum(dual.get((m,v,z&m),0) for m in masks))
        for m in masks:sig[v,m]={z&m for z in patterns}
        total+=max(scores)
    for ds,m in zip(axes,masks):
        cells={}
        for v in domain:cells.setdefault(v&~m,[]).append(v)
        for cube in cells.values():
            best=0
            for k in range(1<<len(cube)):
                vertices={v for j,v in enumerate(cube) if k>>j&1}
                deg={v:sum(d for d in ds if v^d in vertices) for v in vertices}
                if any(z not in sig[v,m] for v,z in deg.items()) or not is_forest(vertices,ds):continue
                best=max(best,-sum(dual.get((m,v,z),0) for v,z in deg.items()))
            total+=best
    assert total==record["upper"]
    return total
def work(job):
    i,level,ep,g,st,u,w=job
    rec=json.loads(Path(f"q9_shell2_integer_certificates/r{level}_goal{g}_parent{i}_e{ep}.json").read_text())
    assert check(rec)==u
    if st=="FOUND":verify(w);assert len(w)-1==g
    else:assert w is None
    if st=="DUAL_EXCLUSION":assert u<rec["scale"]*(g+1)
    return i,ep,g,st
if __name__=="__main__":
    rows=list(map(json.loads,open("q9_shell2_replay_192.jsonl")))
    assert len(rows)==265
    keys={(i,e) for i,level,e,g,*_ in rows if g==192 and level==2}
    assert keys=={(i,e) for i in range(131) for e in (0,1)}
    original=list(map(json.loads,open("q9_contact_shell_duals_192.jsonl")))
    assert rows==original
    parents={}
    for l in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,l.split()))
        if len(p)==192:parents.setdefault(forms(p,191)[0],p)
    refs=list(parents.values())
    for i,level,e,g,st,u,w in rows:
        assert json.loads(Path(f"q9_shell2_integer_certificates/r{level}_goal{g}_parent{i}_e{e}.json").read_text())["parent"]==refs[i]
    with ProcessPoolExecutor(4) as pool:counts=Counter((g,s) for _,_,g,s in pool.map(work,rows,chunksize=2))
    print(json.dumps({str(k):v for k,v in counts.items()},indent=2))
