"""Retry unsolved cube-domain orbits with a larger conflict budget."""
import json
import sys
from pathlib import Path
from itertools import combinations
from retry_q9_six_cube_cycle_cuts import search
from verify_q9_coil_whole_cells import automorphisms, image_key, load, pairwise


if __name__=='__main__':
    cycle=json.loads(Path('q9_coil_open_191_witness.json').read_text())['cycle']
    seed=set(cycle);group=list(automorphisms(cycle));seen={};previous=[]
    for p in sys.argv[2:]:
        previous.extend(load(p))
    for r in previous:
        key=tuple(r['axes']),tuple(r['cells'])
        rep=min(image_key(key,perm,shift) for perm,shift in group)
        if r['status']!='UNKNOWN' or rep not in seen:seen[rep]=r['status']
    for (axes,cells),status in seen.items():
        if status!='UNKNOWN':continue
        domain={v for v in range(512) if sum(((v>>a)&1)<<i for i,a in enumerate(axes)) in cells}
        fixed=seed-domain
        status,w=search(fixed,seed,192,int(sys.argv[1]),allowed=fixed|domain)
        if w:pairwise(w,len(w)-1);assert len(w)>=193 and set(w)-domain==fixed
        print(json.dumps(dict(axes=axes,cells=cells,fixed=len(fixed),target=192,status=status,witness=w),separators=(',',':')),flush=True)
        if w:break
