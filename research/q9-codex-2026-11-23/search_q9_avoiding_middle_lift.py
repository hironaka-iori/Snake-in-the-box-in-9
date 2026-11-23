from concurrent.futures import ProcessPoolExecutor
from search_q9_two_tip_lift import work
from verify_q9_center_avoidance import forms,verify
import os,json
if __name__=="__main__":
    keys={bytes(map(int,w)) for w in open("q9_excluded_142_lex.txt").read().split()}
    assert len(keys)==17974
    words=open("q8_two_crossing_middle_seeds.txt").read().split()
    # Favor the variants with the most surviving contacts to the old upper forest.
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(work,((i,w,ep,190) for i,w in enumerate(words[:408]) for ep in (0,1)),chunksize=1):
            if r[-1]:
                verify(r[-1]);assert len(r[-1])==191 and keys.isdisjoint(forms(r[-1],142))
            print(json.dumps(r,separators=(",",":")),flush=True)
