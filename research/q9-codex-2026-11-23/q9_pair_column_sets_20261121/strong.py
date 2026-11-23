from positive_only import job
from enhanced import *
ap=argparse.ArgumentParser();ap.add_argument('prior');ap.add_argument('budget',type=int);ap.add_argument('--positive-only',action='store_true');op=ap.parse_args()
for l in Path(op.prior).read_text().splitlines():
    old=json.loads(l)
    if old['status']!='UNKNOWN':continue
    i=old['id']
    if op.positive_only:p,aa,b,us,k,j,drop=job(i)
    else:p,aa,us,k,mode=case(i);b=[split(p,a) for a in aa]
    r=solve(p,aa,us,193,op.budget,base_override=b);r.update(id=i,axes=aa);print(json.dumps(r,separators=(',',':')),flush=True)
    if r['status']=='FOUND':break
