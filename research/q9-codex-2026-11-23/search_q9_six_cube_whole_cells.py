"""Keep all occupied vertices outside a set of Q6 fibers; inside use any subset."""
import json
import sys
from itertools import combinations
from pathlib import Path
from retry_q9_six_cube_sites_cadical import load, search
from search_q9_wynn_plateau import verify

def run(source, count, target, budget):
    seen=set()
    for row,line in enumerate(source.read_text().splitlines()):
        seq=load(line)
        seed=set.union(*(portion for _,portion in seq))
        for cells in combinations(range(8),count):
            fixed=frozenset(v for v in seed if v>>6 not in cells)
            key=(fixed,cells)
            if key in seen:continue
            seen.add(key)
            allowed=fixed|{v for v in range(512) if v>>6 in cells}
            st,w=search(set(fixed),seed,target,budget,allowed=allowed)
            if w:
                assert verify(w) and len(w)>=target+1
                assert fixed=={v for v in w if v>>6 not in cells}
            yield dict(row=row,cells=cells,fixed=len(fixed),target=target,status=st,witness=w)
            if w and target>=192:return

if __name__=='__main__':
    for record in run(Path(sys.argv[1]),*map(int,sys.argv[2:])):
        print(json.dumps(record,separators=(',',':')),flush=True)
        if record['target']==191 and record['witness']:break
