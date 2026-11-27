"""Search for partners after deleting arbitrary sites, keeping the fixed 98-edge arm."""
from argparse import ArgumentParser
from itertools import combinations
from hashlib import sha256
import sys
from inputs276 import HERE,MS,read,save
from partners import cases,witness
sys.path.insert(0,str(MS/"274-rebuilding-near-a-fixed-arm"))
from replay_near import _enumerate_mask

def main():
    ap=ArgumentParser();ap.add_argument("--radius",type=int,default=2);ap.add_argument("--visits",type=int,default=1);args=ap.parse_args()
    roots=cases();f=HERE/"placements.json";out=read(f)
    fp=HERE/"scattered-partners.json";led=read(fp) if fp.exists() else {}
    for key,r in roots.items():
        A=r["parent"];dest=out[key];oldcoords=dest["best"]["partner"];ceiling=r["old"]["upper"]-98
        rows=led.setdefault(key,{})
        pool={bytes(oldcoords)}
        for row in rows.values():
            pool.update(bytes(q) for q in row["peers"])
        for step in range(args.visits):
            pending=sorted((q for q in pool if bytes(q).hex()+":"+str(args.radius) not in rows),key=lambda q:(-len(q),sha256(q).digest()))
            if not pending:break
            seed=pending[0];old=sum(1<<v for v in seed);blocked=old|sum(1<<v for v in A)
            peers=set();details=[]
            for d in range(args.radius+1):
                count=0;totals={}
                for cut in combinations(range(1,len(seed)),d):
                    keep=old^sum(1<<seed[i] for i in cut);count+=1
                    for p in _enumerate_mask(blocked,keep,len(seed),ceiling):
                        if p[0]!=0:continue
                        b=bytes(p);assert set(seed)-set(b)=={seed[i] for i in cut}
                        peers.add(b);totals[len(p)-1]=totals.get(len(p)-1,0)+1
                details.append(dict(deletions=d,cases=count,lengths=totals))
            assert seed in peers
            best=min(peers,key=lambda p:(-len(p),p));w=witness(A,list(best))
            if w["edges"]>dest["best"]["edges"]:
                dest["best"]=w;save(f,out)
            pool.update(peers);rows[seed.hex()+":"+str(args.radius)]=dict(seed=list(seed),radius=args.radius,levels=details,peers=[list(p) for p in sorted(peers)])
            save(fp,led)
            print("Arbitrary partner deletions",key,step,"seed",len(seed)-1,"longest",len(best)-1,"peers",len(peers),flush=True)
if __name__=="__main__":main()
