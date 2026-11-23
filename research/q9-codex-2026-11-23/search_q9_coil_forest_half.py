"""Fix one complete Q8 layer of the Q9 coil and allow an arbitrary partner forest."""
import json
from pathlib import Path
import sys
from retry_q9_six_cube_cycle_cuts import search
from verify_q9_six_cube_coverage import pairwise
from search_q9_wynn_plateau import NB


def stats(fixed):
    left=set(fixed);sizes=[]
    while left:
        todo=[left.pop()]
        for v in todo:
            for w in NB[v]:
                if w in left:left.remove(w);todo.append(w)
        sizes.append(len(todo))
    return sorted(sizes,reverse=True)


if __name__=='__main__':
    seed=set(json.loads(Path('q9_coil_open_191_witness.json').read_text())['cycle'])
    target,budget=map(int,sys.argv[1:])
    for axis in range(9):
        for side in range(2):
            domain={v for v in range(512) if (v>>axis)&1==side}
            fixed=seed-domain
            status,w=search(fixed,seed,target,budget,allowed=fixed|domain)
            if w:
                pairwise(w,len(w)-1)
                assert len(w)>=target+1 and set(w)-domain==fixed
            print(json.dumps(dict(axis=axis,side=side,fixed=len(fixed),components=stats(fixed),target=target,status=status,witness=w),separators=(',',':')),flush=True)
            if w and target>=192:raise SystemExit(0)
