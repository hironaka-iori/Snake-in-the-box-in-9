from octsolve import *
ap=argparse.ArgumentParser();ap.add_argument('budget',type=int);ap.add_argument('--prior');args=ap.parse_args()
selected=[0,13,37,58,71,94,113,130]
ids=range(72) if not args.prior else [x['id'] for l in Path(args.prior).read_text().splitlines() if (x:=json.loads(l))['status']=='UNKNOWN']
for i in ids:
    k=selected[i//9];a=i%9;b=(a+1)%9;p=bank[k];aa=[a,b];c=split(p,a)
    us=[split(cube,a)-c,split(cube,b)]
    v=solve(p,aa,us,193,args.budget,require_new=False);v.update(id=i,source=k,axis=a,phase_axis=b,mandatory=len(c));print(json.dumps(v,separators=(',',':')),flush=True)
    if v['status']=='FOUND':break
