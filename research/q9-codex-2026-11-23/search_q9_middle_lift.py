from concurrent.futures import ProcessPoolExecutor
from grow_q8_two_crossing_middles import collect
from grow_q8_exchange_bank import norm
from verify_q9_center_avoidance import verify
from search_q9_two_tip_lift import work
import json,sys
if __name__=="__main__":
    controls=[]
    for i,(p,f) in enumerate(collect()):
        options=[f] if len(f)==191 else [f[:-1],f[1:]]
        for w in options:
            verify(w)
            if len(w)==191 and w[0]>=256 and w[-1]>=256:
                ep=((w[0]-256)^p[0]).bit_count()%2
                controls.append((-1-i,norm(p),ep,190));break
    words=open("q8_two_crossing_middle_seeds.txt").read().split()
    limit=int(sys.argv[1]);start=int(sys.argv[2]) if len(sys.argv)>2 else 0
    jobs=(controls if start==0 else [])+[(i,words[i],e,192) for i in range(start,min(len(words),start+limit)) for e in (0,1)]
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(work,jobs,chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[0]>=0 and r[-1]:break
