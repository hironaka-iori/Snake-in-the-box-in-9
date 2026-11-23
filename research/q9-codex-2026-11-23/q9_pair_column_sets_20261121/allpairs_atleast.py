from atleast import *
ap=argparse.ArgumentParser();ap.add_argument('budget',type=int);ap.add_argument('--prior');a=ap.parse_args()
selected=[0,13,37,58,71,94,113,130]
pairs=list(itertools.combinations(range(9),2))
jobs=range(36*len(selected)) if a.prior is None else [x['id'] for l in Path(a.prior).read_text().splitlines() if (x:=json.loads(l))['status']=='UNKNOWN']
for i in jobs:
    k=selected[i//36];aa=pairs[i%36];p=bank[k];o=[split(p,d) for d in aa]
    us=[split(cube,d)-c for d,c in zip(aa,o)]
    r=solve(p,aa,us,193,a.budget,require_new=False);r.update(id=i,source=k,axes=aa,mandatory=list(map(len,o)));print(json.dumps(r,separators=(',',':')),flush=True)
    if r['status']=='FOUND':break
