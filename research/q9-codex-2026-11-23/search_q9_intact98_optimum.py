"""Find the optimum conditional on the specified intact lower slice."""
from search_q9_punctured_q8 import run
from verify_q9_center_avoidance import verify
from concurrent.futures import ThreadPoolExecutor
import json
if __name__=="__main__":
    arm=json.loads(open("q8_free_layer_full98_duals.jsonl").readline())["certificate"]["arm"]
    for g in range(192,140,-1):
        colours=(0,1) if g%2==0 else (0,)
        with ThreadPoolExecutor(len(colours)) as pool:
            results=list(pool.map(run,[((),ep,g,arm) for ep in colours]))
        for r in results:
            print(json.dumps(r,separators=(",",":")),flush=True)
        if any(r[-1] for r in results):break
