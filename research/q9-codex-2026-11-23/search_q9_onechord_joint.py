"""Free neighborhoods around both ends of the single chord and reconnect unrestrictedly."""
import argparse
import json
from pathlib import Path
from retry_q9_six_cube_cycle_cuts import search
from verify_q9_six_cube_coverage import pairwise


def center(i,low,high,size):
    off=min(max(low,i-size//2),high-size)
    return set(range(max(low,off),min(high,off+size)))


def pair(path):
    matches=[(i,j) for i,v in enumerate(path) for j in range(i+2,len(path)) if (path[j]^v).bit_count()==1]
    assert len(matches)==1 and len(set(path))==len(path) and all((a^b).bit_count()==1 for a,b in zip(path,path[1:]))
    return matches[0]


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source',type=Path);p.add_argument('target',type=int);p.add_argument('budget',type=int);p.add_argument('sizes',type=int,nargs='+');args=p.parse_args()
    seen=set();cube=set(range(512))
    for row,line in enumerate(args.source.read_text().splitlines()):
        path=list(map(int,line.split()));i,j=pair(path);seed=set(path)
        for n in args.sizes:
            for mode in range(2):
                if mode==0:
                    # Center each neighborhood independently.
                    released=center(i,0,len(path),n)|center(j,0,len(path),n)
                else:
                    # Reserve the interval between the two ends of the chord, free vertices to either side.
                    released=set(range(max(0,i-n+1),i+1))|set(range(j,min(len(path),j+n)))
                fixed=frozenset(v for t,v in enumerate(path) if t not in released)
                if fixed in seen:continue
                seen.add(fixed)
                status,w=search(set(fixed),seed,args.target,args.budget,allowed=cube)
                if w:
                    pairwise(w,len(w)-1);assert len(w)>=args.target+1 and fixed<=set(w)
                print(json.dumps(dict(row=row,chord=[i,j],size=n,mode=mode,fixed=len(fixed),target=args.target,status=status,witness=w),separators=(',',':')),flush=True)
                if w:raise SystemExit(0)
