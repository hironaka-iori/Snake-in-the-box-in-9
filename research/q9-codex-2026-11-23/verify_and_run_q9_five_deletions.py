"""Compare the accelerated final pair search with the prior exhaustive four-deletion run."""
import json,subprocess,math
from concurrent.futures import ProcessPoolExecutor
from search_q9_free_record_slice import parents,verify
from verify_and_run_q9_vertex_exchange import check_control
import verify_and_run_q9_vertex_exchange as original

def run(job):
    i,p,k=job
    result=subprocess.check_output(["/tmp/q9_five_delete20","9",str(k),"--fast-pairs"],input=" ".join(map(str,p))+"\n",text=True).split()
    _,st,n,viable,trials,*raw=result
    w=None
    if st=="FOUND":
        w=list(map(int,raw));verify(w);assert len(w)==193 and len(set(p)-set(w))==k
    else:assert st=="NO" and int(n)==math.comb(192,k)
    return [i,st,int(n),int(viable),int(trials),w]

if __name__=="__main__":
    bank=parents()
    baseline=list(map(json.loads,open("q9_four_delete_192.jsonl")))[1:]
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(run,((i,p,4) for i,p in enumerate(bank)),chunksize=1):
            assert r==baseline[r[0]],(r,baseline[r[0]])
        print(json.dumps({"q9_crosschecks":len(bank),"verified_deletion_choices_per_parent":math.comb(192,4)}),flush=True)
        order=sorted(range(len(bank)),key=lambda i:-baseline[i][3])
        for r in pool.map(run,((i,bank[i],5) for i in order),chunksize=1,buffersize=8):
            print(json.dumps(r),flush=True)
            if r[-1]:break
