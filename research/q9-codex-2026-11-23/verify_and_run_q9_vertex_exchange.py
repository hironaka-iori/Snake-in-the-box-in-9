import json,subprocess,random,math,sys
from concurrent.futures import ProcessPoolExecutor
from collections import Counter
from verify_q9_center_avoidance import verify
from search_q9_free_record_slice import parents
BINARY="/tmp/q9_four_delete_j20"
def check_control():
    paths={}
    def dfs(p):
        paths.setdefault(len(p),[]).append(p)
        for axis in range(4):
            x=p[-1]^(1<<axis)
            if x in p or any((x^y).bit_count()==1 for y in p[:-1]):continue
            dfs(p+[x])
    for x in range(16):dfs([x])
    opts={n:{frozenset(p) for p in paths.get(n+1,[])} for n in paths}
    rng=random.Random(194);counts=Counter()
    for k in (1,2,3,4):
        sample=[p for n,allp in paths.items() if n>k for p in rng.sample(allp,min(10,len(allp)))]
        lines=subprocess.check_output([BINARY,"4",str(k)],input="".join(" ".join(map(str,p))+"\n" for p in sample),text=True).splitlines()
        assert len(lines)==len(sample)
        for p,l in zip(sample,lines):
            i,st,n,_,_,*w=l.split()
            expected=any(len(set(p)-q)==k for q in opts[len(p)])
            assert (st=="FOUND")==expected and (expected or int(n)==math.comb(len(p),k))
            if expected:
                w=list(map(int,w));verify(w);assert len(w)==len(p)+1 and len(set(p)-set(w))==k
            counts[k,st]+=1
    return {str(k):{s:counts[k,s] for s in ("FOUND","NO")} for k in (1,2,3,4)}
def run(job):
    i,p=job;verify(p)
    line=subprocess.check_output([BINARY,"9","4"],input=" ".join(map(str,p))+"\n",text=True)
    _,st,examined,viable,trials,*vertices=line.split()
    if st=="FOUND":
        w=list(map(int,vertices));verify(w);assert len(w)==193 and len(set(p)-set(w))==4
    else:
        assert st=="NO" and int(examined)==math.comb(192,4);w=None
    return i,st,int(examined),int(viable),int(trials),w
if __name__=="__main__":
    print(json.dumps({"independent_Q4_controls":check_control()}),flush=True)
    with ProcessPoolExecutor(4) as pool:
        for row in pool.map(run,enumerate(parents()),chunksize=1,buffersize=8):
            print(json.dumps(row),flush=True)
            if row[-1]:break
