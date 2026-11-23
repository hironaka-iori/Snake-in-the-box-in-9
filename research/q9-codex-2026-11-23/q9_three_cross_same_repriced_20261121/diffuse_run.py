from check import *
def main():
    import random
    ap=argparse.ArgumentParser();ap.add_argument('out');ap.add_argument('--start',type=int,default=0);ap.add_argument('--take',type=int,default=1496);ap.add_argument('--parts',type=int,default=8);ap.add_argument('--sweeps',type=int,default=60);ap.add_argument('--skip',nargs='*',default=[]);args=ap.parse_args()
    skip={(r['i'],r['x']) for r in loadrows(args.skip) if r['bound']<193*r['scale']}
    todo=[(i,x) for i,x in jobs[args.start:] if (i,x) not in skip][:args.take]
    axes=list(itertools.combinations(range(8),3));random.Random(403215).shuffle(axes);axes=axes[:args.parts];masks=[sum(1<<d for d in a) for a in axes]
    with tempfile.TemporaryFile('w+') as f,(D/args.out).open('w') as out:
        for i,x in todo:print(i,x,file=f)
        f.seek(0);proc=subprocess.Popen([str(D/'diffuse'),str(R/'q8_catalogue_96_98.words'),str(args.sweeps),'193',','.join(map(str,masks))],stdin=f,stdout=subprocess.PIPE,text=True)
        for i,x in todo:
            row=proc.stdout.readline().split();assert row and row[0]=='R',row
            a,b,val,scale,bal,e,o,sw=map(int,row[1:]);assert (a,b)==(i,x)
            weights=[]
            for l in proc.stdout:
                if l.startswith('E'):break
                weights.append(list(map(int,l.split())))
            c=dict(scale=scale,axes=axes,weights=weights,balance_weight=bal,end_weights=[e,o])
            p=D/'certs'/f'd{i}_x{x}_dif{args.parts}_{args.sweeps}.json.gz'
            with gzip.open(p,'wt',compresslevel=4) as z:json.dump(c,z,separators=(',',':'))
            print(json.dumps(dict(rank=jobs.index((i,x)),i=i,x=x,scale=scale,bound=val,cert=str(p.relative_to(D)),sweeps=sw)),file=out,flush=True)
        assert proc.wait()==0
if __name__=='__main__':main()
