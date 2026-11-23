from concurrent.futures import ProcessPoolExecutor
from verify_q9_center_avoidance import verify,forms
from pathlib import Path
import json,math,subprocess,os
def run(job):
    i,p,k=job
    raw=subprocess.check_output(["/tmp/q9_exchange_eligible20","9",str(k),"--fast-pairs"],input=" ".join(map(str,p))+"\n",text=True,
                                env=dict(os.environ,Q9_AVOID_SHAPES="q9_excluded_142_lex.txt")).split()
    _,st,count,viable,trials,*v=raw
    if st=="FOUND":
        w=list(map(int,v));verify(w)
        blocked={bytes(map(int,s)) for s in Path("q9_excluded_142_lex.txt").read_text().split()}
        assert len(w)==len(p)+1 and len(set(p)-set(w))==k and blocked.isdisjoint(forms(w,142))
    else:assert int(count)==math.comb(len(p),k);w=None
    return [i,k,st,int(count),int(viable),int(trials),w]
if __name__=="__main__":
    seeds=[r["vertices"] for r in json.load(open("q9_center_avoidance_verified.json"))["new_witnesses"]]
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(run,((i,p,k) for k in (1,2,3,4,5) for i,p in enumerate(seeds)),chunksize=1,buffersize=8):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:
                # Each further hit is subjected to the same strict fragment filter.
                path=r[-1]
                for m in (1,2,3,4):
                    q=run((r[0],path,m))
                    if q[-1]:
                        print(json.dumps(["further",q]),flush=True);path=q[-1]
                        if len(path)>=193:break
                if len(path)>=193:break
