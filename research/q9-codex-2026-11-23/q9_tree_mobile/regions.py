import argparse,collections,gzip,json,random
from search import D,R,P,shade,solve
def cloud(s,p,rng,i):
 if i%2:
    sites=set();centers=rng.sample(list(s),2+i%4)
    if i%5==0:centers[0]=p[0]
    for v in centers:
        varying=rng.sample(range(9),[4,5,6][i%3]);mask=511^sum(1<<d for d in varying)
        sites.update(x for x in P if (v&mask)==(x&mask))
 else:
    tips=[rng.choice(list(s)) for _ in range(1+i%3)];tips[0]=p[0] if i%4==0 else tips[0]
    sites=set(sorted(P,key=lambda x:min((x^v).bit_count() for v in tips)+1.8*rng.random())[:[32,48,64,80][(i//2)%4]])
 return sites
def main():
 ap=argparse.ArgumentParser();ap.add_argument('count',type=int);ap.add_argument('seed',type=int);ap.add_argument('mode');ap.add_argument("--source");args=ap.parse_args();rng=random.Random(args.seed)
 pool=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')] if args.mode=='target' else [r['path'] for l in (D/'growth.log').read_text().splitlines() if (r:=json.loads(l))['kind']=='W']
 if args.source:pool=[r["path"] for l in (D/args.source).read_text().splitlines() if (r:=json.loads(l))["status"]=="FOUND"]
 if args.mode!="target":largest=max(map(len,pool));pool=[p for p in pool if len(p)>=largest-2]
 for i in range(args.count):
    idx=rng.randrange(len(pool));p=pool[idx][:];p=p if rng.randrange(2) else p[::-1];p=shade(p);s=set(p[::2]);area=cloud(s,p,rng,i);r=solve(s,0,[],2,4000,args.seed,idx,None,10,True,cloud=area)
    r.update(i=i,region=len(area),mode='region_'+args.mode,source_length=len(p)-1)
    if r['status']=='FOUND':r['source']=p;r['area']=sorted(area)
    print(json.dumps(r,separators=(',',':')),flush=True)
    if r['status']=='FOUND' and (args.mode=='target' or len(r['path'])>largest):break
if __name__=='__main__':main()
