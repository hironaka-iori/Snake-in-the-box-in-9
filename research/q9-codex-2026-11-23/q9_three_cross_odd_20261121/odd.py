import json,random,sys,itertools,argparse,time,gzip
from pathlib import Path
from collections import defaultdict
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R))
from certify_q9_intact_q8_facet import build
from q9_rigid_facet_ports import word_path
from verify_q9_intact98_all_crossings import integer_bound
bank=(R/'q8_catalogue_96_98.words').read_text().split()
def family():
    jobs=[]
    for i,w in enumerate(bank):
        a=word_path(w);F=set(a);used=F|{v^(1<<d) for v in F for d in range(8)}
        jobs.extend((i,x) for x in sorted(set(range(256))-used))
    assert len(jobs)==1496;return jobs
def case(i,x):
    a=word_path(bank[i]);low=set(a)|{x};m=x.bit_count()%2;ends=[int(c!=m) for c in (0,1)];delta=sum(1-2*(v.bit_count()%2) for v in low)
    return a,low,{a[0],a[-1],x},ends,delta
def rounded(c,L,P,ends,delta):
    F=set(range(256))-(L-P)
    c=dict(c,weights=[w for w in c['weights'] if w[1] in F])
    return integer_bound(c,L,P,ends,delta)+len(L)*c['scale'],c
def run():
    ap=argparse.ArgumentParser();ap.add_argument('kind',choices=['reuse','generate']);ap.add_argument('--parts',type=int,default=4);ap.add_argument('--max',type=int,default=1496);ap.add_argument('--skip',default='');ap.add_argument('--outfile',required=True);ap.add_argument('--shard',default='0/1');ap.add_argument('--start',type=int,default=0);args=ap.parse_args()
    apath=list(itertools.combinations(range(8),3));random.Random(403215).shuffle(apath);jobs=family()
    skip=set()
    for fname in args.skip.split(','):
        if fname:
            for line in (D/fname).open():
                r=json.loads(line)
                if r['bound']<194*r['scale']:skip.add((r['i'],r['x']))
    donor=defaultdict(list)
    if args.kind=='reuse':
        for f in sorted((R/'q9_catalogue_three_cross/cases').glob('*.json')):
            try:r=json.loads(f.read_text())
            except ValueError:continue
            donor[int(f.stem.split('_')[0][1:])].append((f,r['cert']))
    certs=D/'certs';certs.mkdir(exist_ok=True)
    # A donor/extra combination is always independent of other cases.
    take,mod=map(int,args.shard.split('/'));done=0
    with (D/args.outfile).open('w') as out:
        for rank,(i,x) in enumerate(jobs):
            if rank<args.start or rank%mod!=take or (i,x) in skip:continue
            a,L,P,ends,delta=case(i,x);w=bank[i]
            def record(bound,c,file):
                row=dict(rank=rank,i=i,x=x,low=len(L),ends=ends,delta=delta,bound=bound,scale=c['scale'],cert=file)
                print(json.dumps(row,separators=(',',':')),file=out,flush=True)
            if args.kind=='reuse':
                options=sorted(donor[i],key=lambda z:z[0].stem!=f'd{i}_x{x}')
                if not options:continue
                best=None
                for f,c in options[:3]:
                    v,c=rounded(c,L,P,ends,delta)
                    if best is None or v<best[0]:best=(v,c,f)
                    if v<194*c['scale']:break
                v,c,f=best
                # Freeze exact certificate used locally, independent of the live even-target task.
                dest=certs/f'{f.stem}_prior.json.gz'
                if not dest.exists():
                    with gzip.open(dest,'wt') as g:json.dump(c,g,separators=(',',':'))
                record(v,c,str(dest.relative_to(D)))
            else:
                res=build(a,P,L,ends,delta,apath[:args.parts])
                if res is None:raise RuntimeError(('empty',i,x))
                const,s,t,c=res;v=const+len(L)*s+sum(table[0][2] for _,table in t)
                dest=certs/f'd{i}_x{x}_a{args.parts}.json.gz'
                with gzip.open(dest,'wt') as g:json.dump(c,g,separators=(',',':'))
                record(v,c,str(dest.relative_to(D)))
            done+=1
            if done>=args.max:break
if __name__=='__main__':run()
