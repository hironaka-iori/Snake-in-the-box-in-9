from run_q9_rotation_quotient import work
from concurrent.futures import ProcessPoolExecutor
import json
if __name__=="__main__":
    jobs=[]
    for w in range(1,10):
        cls=((1,0),)*(9-w)+((1,1),)*w
        # XOR by any vector commutes with the order-two translation. Any orbit can start the cycle.
        for goal in (194,196,198):jobs.append((cls,goal,50000000,0,1))
    with ProcessPoolExecutor(3) as p:
        for r in p.map(work,jobs,chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
