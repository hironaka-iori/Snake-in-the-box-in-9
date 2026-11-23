"""Search for any single-crossing completion of the newly generated Q8 arms."""
from concurrent.futures import ProcessPoolExecutor
from contextlib import redirect_stdout
from io import StringIO
from itertools import combinations
import json,random,subprocess,sys
from search_q8_free_layer_dual import solve
from verify_q8_free_layer_dual import verify as check_bound
from export_q8_search_factors import emit
from verify_q9_center_avoidance import verify
def work(job):
    i,word=job;p=[0]
    for c in word:p.append(p[-1]^(1<<int(c)))
    axes=list(combinations(range(8),3));random.Random(314).shuffle(axes)
    target=193-len(p)
    r=solve(p,axes[:12],(target-1)%2)
    r.update(index=i,lower_edges=len(p)-1,target_vertices=target,total_edges=192)
    if "certificate" not in r:return i,word,"UNKNOWN",None,r
    check_bound(r)
    if r["vertices_upper"]<target:return i,word,"DUAL_EXCLUSION",None,r
    s=StringIO()
    with redirect_stdout(s):emit(r)
    line=subprocess.check_output(["/tmp/q8_exchange_conditioned20","160000","walk"],input=s.getvalue(),text=True)
    idx,st,nodes,*raw=line.split()
    assert int(idx)==i and st in ("FOUND","UNKNOWN","EXHAUSTED")
    w=None
    if st=="FOUND":
        w=list(map(int,raw));verify(w);assert len(w)==193 and w[:len(p)]==p[::-1]
    r["branch_nodes"]=int(nodes)
    return i,word,st,w,r
if __name__=="__main__":
    filename=sys.argv[1] if len(sys.argv)>1 else "q8_exchange_new_rooted_arms.txt"
    words=sorted(open(filename).read().split(),key=lambda s:(-len(s),s))
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(work,enumerate(words),chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[3]:break
