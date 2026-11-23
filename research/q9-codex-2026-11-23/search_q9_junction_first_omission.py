"""Partition the radius-eight, even-endpoint case by the first omitted old anchor."""
import json
import sys
from pathlib import Path
from search_q9_junction_last_cases import Balanced, anchored, check, sources

def main():
    _,_,p,joins=next(sources(Path(sys.argv[1])))
    dist=[min(abs(i-c) for c in [0,*joins,len(p)-1]) for i in range(len(p))]
    fixed={v for v,d in zip(p,dist) if d>8}
    rim=[v for v,d in zip(p,dist) if d==8]
    assert len(fixed)==75 and len(rim)==12
    for omitted in rim:
        ep=0
        anchored.Minicard=lambda:Balanced(ep,fixed,192)
        status,w=anchored.search(fixed,set(p),192,int(sys.argv[2]),allowed=set(range(512))-{omitted})
        if w:
            check(w,192)
            assert len(w)==193 and fixed<=set(w) and omitted not in w
        print(json.dumps(dict(fixed=sorted(fixed),omitted=omitted,status=status,witness=w)),flush=True)
        if w:return
        fixed.add(omitted)
if __name__=="__main__":
    main()
