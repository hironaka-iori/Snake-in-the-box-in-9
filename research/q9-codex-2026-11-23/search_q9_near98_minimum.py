"""Search paths of all lengths >=192 containing all but at most one specified Q8 vertex."""
from search_q9_punctured_q8 import run
from search_q9_shell_dual import solve
from concurrent.futures import ProcessPoolExecutor
import json,os
if __name__=="__main__":
    assert os.getenv("Q9_PATH_MINIMUM") and os.getenv("Q9_FREE_BOTTOM")
    arm=json.loads(open("q8_free_layer_full98_duals.jsonl").readline())["certificate"]["arm"]
    # Fix a known 99-vertex snake and demand >=97 vertices of its endpoint parity.
    # A 97-vertex subset cannot contain all 99 mandatory vertices.
    c=solve((0,arm,0,arm[0].bit_count()%2,96,1000,arm,set(arm)))
    assert c[4]=="FOUND" and len(c[-1])==99;print(json.dumps(c),flush=True)
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(run,[((j,),ep,g,arm) for j in range(99) for g,ep in [(192,0),(192,1),(193,0)]],chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
