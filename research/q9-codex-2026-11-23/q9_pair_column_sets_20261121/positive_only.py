from run import *
def job(i):
    rng=random.Random(681943+i);k=i%131;p=bank[k];a,b=rng.sample(range(9),2);aa=[a,b];orig=[split(p,d) for d in aa];source2=k
    if (i//131)%2:
        choices=[]
        for j,q in enumerate(bank):
            qB=split(q,b);h=len(qB^orig[1]);g=len(split(q,a)^orig[0])
            if h and g:choices.append((h+g,j,qB))
        choices.sort(key=lambda z:z[0]);_,source2,orig[1]=rng.choice(choices[:min(10,len(choices))])
    n=(0,2,5,9,16,24)[i%6]
    omit=[set(rng.sample(sorted(c),n)) for c in orig]
    patches=[split(cube,axis)-c|o for axis,c,o in zip(aa,orig,omit)]
    return p,aa,orig,patches,k,source2,n
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('n',type=int);ap.add_argument('budget',type=int);ap.add_argument('--prior');args=ap.parse_args()
    ids=range(args.n) if args.prior is None else [x['id'] for l in Path(args.prior).read_text().splitlines() if (x:=json.loads(l))['status']=='UNKNOWN']
    for i in ids:
        p,aa,base,us,k,j,drop=job(i);v=solve(p,aa,us,193,args.budget,base_override=base)
        v.update(id=i,source=k,donor=j,axes=aa,omitted=drop,mandatory=[len(s-u) for s,u in zip(base,us)]);print(json.dumps(v,separators=(',',':')),flush=True)
        if v['status']=='FOUND':break
