"""Recheck unresolved transfers using the exact pair occupancy of the original job."""
from concurrent.futures import ProcessPoolExecutor
import gzip,json,sys
from q9_pair_selector import search
from verify_q9_center_avoidance import forms,verify

def load_paths():
    bank={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192: bank.setdefault(forms(p,191)[0],p)
    for p in bank.values():verify(p)
    return list(bank.values())

def init():
    global paths
    paths=load_paths()

def job(args):
    row,budget=args
    i,s,t,v,y,_,_=row
    p=paths[i]; side=set(p[s::2])
    trial=side-{next(w for w in (v,v^t) if w in side)}
    trial.add(next(w for w in (y,y^t) if w not in side))
    pairs=[(w,w^t) for w in sorted(trial) if (w^t) not in trial]
    st,w=search(trial,pairs,t,set(p),192,budget)
    if w:
        verify(w);assert len(w)==193
        m=set(w[1::2]);assert all((a in m)+(a^t in m)==(a in trial)+(a^t in trial) for a in range(512))
    return [i,s,t,v,y,st,w]

if __name__=="__main__":
    args=[(r,int(sys.argv[2])) for r in map(json.loads,open(sys.argv[1])) if r[5]=="UNKNOWN"]
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for row in pool.map(job,args,chunksize=5):
            print(json.dumps(row,separators=(",",":")),flush=True)
            if row[6]:break
