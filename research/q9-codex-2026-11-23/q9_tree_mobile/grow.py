import argparse,collections,json,random
from search import D,M,match,solve
def main():
 ap=argparse.ArgumentParser();ap.add_argument('seed',type=int);ap.add_argument('limit',type=int);ap.add_argument('width',type=int);args=ap.parse_args();rng=random.Random(args.seed)
 start=json.loads((D/'verified.json').read_text())['best_tree_witness']['path'];pool=[start];node_id=0
 while pool:
    nexts={};stats=collections.Counter();work=0;level=len(pool[0])-1
    for q,p in enumerate(pool):
        assert len(p)==level+1
        base=set(p[::2]);src=min(base);tips=(p[0],p[-1]);local=list(M);rng.shuffle(local)
        for j in range(args.limit):
            m=local[j%len(local)];fr=match(base,m);rng.shuffle(fr);width=[10,15,21,29,38,50][j%6]
            if j%4!=3:
                ranks={v: min((v^t).bit_count() for t in tips)+rng.random()*3.5 for v in base}
                fr.sort(key=lambda pair:ranks[pair[0]])
            fr=fr[:width];mn=1+j%2
            r=solve(base,m,fr,mn,2500,args.seed,q,None,8,True)
            work+=1;stats[r['status']]+=1
            if r['status']=='FOUND':
                k=tuple(sorted(r['path'][::2]))
                if k in nexts:continue
                nexts[k]=r['path'];print(json.dumps(dict(kind='W',previous_length=level,parent=q,free=fr,minimum=mn,**{k:v for k,v in r.items() if k not in ('free',)}),separators=(',',':')),flush=True)
                if level+2>=192:break
                if j<args.limit//2 and len(nexts)<args.width:continue
            if len(nexts)>=args.width:break
        if len(nexts)>=args.width or level+2>=192:break
    print(json.dumps(dict(kind='level',length=level,parents=len(pool),trials=work,status=stats,unique_next=len(nexts))),flush=True)
    if level+2>=192:break
    pool=list(nexts.values())
if __name__=='__main__':main()
