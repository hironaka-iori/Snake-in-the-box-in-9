"""Try to add at least two steps by replacing one window of an exact 190-edge path."""
import argparse,csv,json,random
from pathlib import Path
from repair_q9_contiguous_corridor import norm,search
from verify_q9_six_cube_coverage import pairwise
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('bank',type=Path);ap.add_argument('width',type=int);ap.add_argument('per',type=int);ap.add_argument('budget',type=int);ap.add_argument('salt',type=int)
    a=ap.parse_args();seen=set();r=random.Random(a.salt)
    with a.bank.open() as f:paths=[list(map(int,x['vertices'].split())) for x in csv.DictReader(f)]
    order=list(range(len(paths)));r.shuffle(order)
    for row in order:
        p=paths[row];pairwise(p,190)
        starts=sorted({0,len(p)-a.width,*r.sample(range(1,len(p)-a.width),a.per)})
        for s in starts:
            key=norm(p,s,a.width)
            if key in seen:continue
            seen.add(key)
            st,w=search(p,s,a.width,a.budget,True,2)
            if w:pairwise(w,len(w)-1);assert len(w)>=193
            print(json.dumps(dict(row=row,start=s,width=a.width,target=192,status=st,witness=w),separators=(',',':')),flush=True)
            if w:raise SystemExit(0)
