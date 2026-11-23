from concurrent.futures import ProcessPoolExecutor
from collections import Counter
from pathlib import Path
import json
from grow_q8_exchange_bank import norm,collect
if __name__=="__main__":
    seeds=set(Path("q8_exchange_new_rooted_arms.txt").read_text().split())
    old=set(Path("q8_joint_even_arms.txt").read_text().split())
    bank={}
    for w in sorted(old|seeds):
        if len(w)<96:continue
        p=[0]
        for c in w:p.append(p[-1]^(1<<int(c)))
        key=min(norm(p),norm(p[::-1]));bank.setdefault(key,p)
    jobs=[]
    for key,p in bank.items():
        for gain in (0,1):
            if len(key)+gain>98:continue
            if key in seeds:jobs.extend((p,k,gain) for k in (1,2,3,4))
            if len(key)>=97:jobs.append((p,5,gain))
    new=set()
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(collect,jobs,chunksize=1):new.update(r)
    new-=old|seeds
    Path("q8_exchange_second_rooted_arms.txt").write_text("".join(w+"\n" for w in sorted(new)))
    print(json.dumps({"jobs":len(jobs),"by_edges":Counter(map(len,new))}))
