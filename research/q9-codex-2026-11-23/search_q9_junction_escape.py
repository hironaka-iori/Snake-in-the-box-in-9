"""Try leaving the excluded 75-anchor family by omitting one or more junction anchors."""
from argparse import ArgumentParser
import json
from pathlib import Path
import search_q9_junction_cells as cells

def main():
    ap=ArgumentParser()
    ap.add_argument("folder",type=Path)
    ap.add_argument("--budget",type=int,default=20000)
    args=ap.parse_args()
    cells.mask_index=cells.index_masks()
    cells.layouts=list(cells.partitions())
    _,_,p,joins=next(cells.sources(args.folder))
    dist=[min(abs(i-s) for s in [0,*joins,len(p)-1]) for i in range(len(p))]
    fixed={v for v,d in zip(p,dist) if d>9}
    ring=[v for v,d in zip(p,dist) if d==9]
    assert len(fixed)==63 and len(ring)==12
    for omitted in ring:
        for ep in (0,1):
            cells.anchored.Minicard=lambda:cells.CellSolver(ep,fixed,192)
            status,w=cells.anchored.search(fixed,set(p),192,args.budget,
                                          allowed=set(range(512))-{omitted})
            if w:
                cells.check(w,192)
                assert len(w)==193 and fixed<=set(w) and omitted not in w
            print(json.dumps(dict(fixed=sorted(fixed),omitted=omitted,ep=ep,
                                  status=status,witness=w)),flush=True)
            if w:return
        fixed.add(omitted)
if __name__=="__main__":main()
