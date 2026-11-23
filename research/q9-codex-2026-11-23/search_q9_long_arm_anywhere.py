"""Search all Q9 extensions of each >=96-edge Q8 shape in the four local banks."""
import json,os
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from search_q9_punctured_q8 import run
from verify_q9_center_avoidance import verify,forms
def arms():
    bank={}
    for name in ("q8_joint_even_arms.txt","q8_exchange_new_rooted_arms.txt","q8_exchange_second_rooted_arms.txt","q8_two_crossing_middle_seeds.txt"):
        for word in Path(name).read_text().split():
            if len(word)<96:continue
            p=[0]
            for d in word:p.append(p[-1]^1<<int(d))
            verify(p);assert max(p)<256
            bank.setdefault(forms(p,len(word))[0],p)
    return sorted(bank.items(),key=lambda item:(-len(item[0]),item[0]))
def work(job):
    k,p,ep,g=job
    return [k.hex(),*run(((),ep,g,p))[1:]]
if __name__=="__main__":
    assert os.getenv("Q9_PATH_MINIMUM") and os.getenv("Q9_FREE_BOTTOM")
    bank=arms();assert len(bank)==197
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(work,[(k,p,e,g) for k,p in bank for e,g in [(0,192),(1,192),(0,193)]],chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
