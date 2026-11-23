"""Check base paths, pair-domain coverage, and solver status manifest.

Run with --replay to rerun every decision using the separate Minicard encoding.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path


def pairwise(path, edges):
    assert len(path)==edges+1==len(set(path))
    assert all(0<=v<512 for v in path)
    assert all(((a^path[j]).bit_count()==1)==(i+1==j)
               for i,a in enumerate(path) for j in range(i+1,len(path)))


def unpack(row):
    words=row.split()
    n=int(words[0]);assert len(words)==1+2*n
    sets=[{64*int(words[1+2*j])+v for v in range(64) if int(words[2+2*j],16)>>v&1}
          for j in range(n)]
    union=set.union(*sets)
    def nb(v):return union & {v^1<<d for d in range(9)}
    ends=[v for v in union if len(nb(v))==1]
    assert len(ends)==2
    path=ends[:1];seen=set(path)
    while len(path)<len(union):
        w,=nb(path[-1])-seen;path.append(w);seen.add(w)
    pairwise(path,191)
    return union


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--replay',action='store_true')
    parser.add_argument('--budget',type=int,default=10000)
    parser.add_argument('--width',type=int,default=2)
    args=parser.parse_args()
    basedir=Path(__file__).resolve().parent
    origins=[unpack(l) for l in (basedir/'q9_six_cube_revisit_191_templates.txt').read_text().splitlines()]
    label={2:'pair',3:'triple'}[args.width]
    answers=[json.loads(l) for l in (basedir/f'q9_six_cube_whole_cells_{label}_192.jsonl').read_text().splitlines()]
    result={(r['row'],tuple(r['cells'])):r for r in answers}
    assert len(result)==len(answers)
    deep=basedir/f"q9_six_cube_whole_cells_{label}_192_deep.jsonl"
    if deep.exists():
        refined=[json.loads(l) for l in deep.read_text().splitlines()]
        for r in refined:
            key=(r["row"],tuple(r["cells"]))
            old=result[key]
            assert old["status"]=="UNKNOWN" and old["fixed"]==r["fixed"] and old["target"]==r["target"]
            result[key]=r
    seen=set();hits=Counter();checks=Counter()
    for i,seed in enumerate(origins):
        for cells in combinations(range(8),args.width):
            others=frozenset(v for v in seed if v//64 not in cells)
            k=(cells,others)
            if k in seen:continue
            seen.add(k)
            r=result.pop((i,cells))
            assert r['fixed']==len(others) and r['target']==192 and r['status'] in ('UNSAT','UNKNOWN','FOUND')
            if r['witness']:pairwise(r['witness'],len(r['witness'])-1);assert len(r['witness'])>=193
            hits[r['status']]+=1
            if args.replay:
                from search_q9_anchored_sets import search
                fixed=set(others)
                allowed=fixed|{v for v in range(512) if v//64 in cells}
                st,w=search(fixed,seed,192,args.budget,allowed=allowed,at_least=True)
                if w:pairwise(w,len(w)-1);assert len(w)>=193
                assert not (w and r['status']=='UNSAT')
                checks[st]+=1
    assert not result
    control=json.loads((basedir/'q9_six_cube_whole_cells_control.jsonl').read_text())
    pairwise(control['witness'],191)
    print(json.dumps({'templates':len(origins),'distinct_domains':len(seen),
                      'logged':hits,'independent_replay':checks}))
