"""Retry unresolved parity cuts with the independent vertex encoding."""
from concurrent.futures import ProcessPoolExecutor
import json,sys
from search_q9_free_record_slice import parents,verify,search

def init():
    global bank
    bank=parents()

def job(row):
    i,m,s,cap,at_least=row;p=bank[i]
    fixed={v for v in p if (v&m).bit_count()%2==s}
    domain=fixed|{v for v in range(512) if (v&m).bit_count()%2!=s}
    st,w=search(fixed,set(p),192,cap,allowed=domain,at_least=at_least)
    if w:
        verify(w);assert len(w)>=193 and (at_least or len(w)==193) and set(w)-{v for v in w if (v&m).bit_count()%2!=s}==fixed
    return [i,m,s,st,w]
if __name__=="__main__":
    if sys.argv[1].startswith("weight="):
        weight=int(sys.argv[1].split("=")[1])
        count=int(sys.argv[4]) if len(sys.argv)>4 else len(parents())
        jobs=[(i,m,s,int(sys.argv[2]),"--at-least" in sys.argv[3:]) for i in range(count)
              for m in range(1,512) if m.bit_count()==weight for s in (0,1)]
    else:jobs=[(i,m,s,int(sys.argv[2]),'--at-least' in sys.argv[3:]) for i,m,s,st,w in map(json.loads,open(sys.argv[1])) if st=="UNKNOWN"]
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for row in pool.map(job,jobs,chunksize=2):
            print(json.dumps(row,separators=(",",":")),flush=True)
            if row[-1]:break
