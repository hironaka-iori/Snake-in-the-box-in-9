from concurrent.futures import ProcessPoolExecutor
from search_q9_two_tip_lift import work
import json
if __name__=="__main__":
    words=open("q8_two_crossing_middle_seeds.txt").read().split()
    left=[(i,words[i],ep,192) for i,ep,g,st,u,w in map(json.loads,open("q9_compatible_middles_192.jsonl")) if i>=0 and st=="UNKNOWN"]
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(work,left,chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
