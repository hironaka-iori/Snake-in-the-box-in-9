"""Replay selected free-facet jobs using explicit minimum semantics and a supplied C++ executable."""
import argparse
import json
import os
from pathlib import Path

from verify_q9_96_donor_coverage import TARGETS, vertices, canonical, check
from search_q9_shell_dual import solve

def test_controls():
    w = json.loads(Path('q9_97_donor_verified_witness.json').read_text())['q9_vertices']
    for p in [w,w[:-1],w[1:]]:
        goal=len(p)-3
        colour=p[0].bit_count()%2 if goal%2==0 else 0
        result=solve((0,p,0,colour,goal,64,set(p),set(p)))
        _,_,_,_,status,_,found=result
        check(status=='FOUND' and len(found)==len(p) and set(found)==set(p), 'minimum-mode positive control failed')
        print(json.dumps(dict(control=True,status=status,target=goal,actual=len(found)-1,ep=colour)),flush=True)

def main():
    a=argparse.ArgumentParser()
    a.add_argument('binary',type=Path)
    a.add_argument('words',nargs='*',help='canonical 96-step words to test')
    a.add_argument('--catalogue',action='store_true',help='test all 726 catalogue donors')
    a.add_argument('--cap',type=int,default=1900000)
    t=a.parse_args()
    os.environ.update(Q9_PATH_MINIMUM='1',Q9_FREE_BOTTOM='1',Q9_SHELL_SOLVER=str(t.binary.resolve()),Q9_SHELL_PARTS='10')
    os.environ.pop('Q9_AVOID_SHAPES',None)
    test_controls()
    known={w for w in Path('q8_catalogue_96_98.words').read_text().split() if len(w)==96}
    for word in (sorted(known) if t.catalogue else t.words):
        check(word in known and canonical(word)==word,'outside 96 catalogue')
        p=vertices(word);fixed=set(p)
        # Build the entire Q9 domain compatible with already-fixed degrees.
        degree={v:sum(v^(1<<d) in fixed for d in range(8)) for v in fixed}
        domain={v+256 for v in range(256) if degree.get(v,0)<2}|fixed
        for v in set(range(256))-fixed:
            neighbors={v^(1<<d) for d in range(8)}&fixed
            if len(neighbors)<=2 and all(degree[x]<2 for x in neighbors): domain.add(v)
        for ep,g in sorted(TARGETS):
            row=solve((0,p,0,ep,g,t.cap,fixed,domain))
            print(json.dumps([word,ep,g,*row[4:]],separators=(',',':')),flush=True)
if __name__=='__main__':main()
