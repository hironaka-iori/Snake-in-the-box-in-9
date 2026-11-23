from ordered_colors import lift,violations,D
from itertools import combinations
import random,sys,json,hashlib
def partitions():
    axes=set(range(9))
    for a in combinations(range(1,9),2):
        g=(0,*a);others=axes-set(g);first=min(others)
        for b in combinations(sorted(others-{first}),2):
            h=(first,*b)
            yield [g,h,tuple(sorted(others-set(h)))]
def main():
    rng=random.Random(7518812);gs=list(partitions());assert len(gs)==280
    rng.shuffle(gs)
    done=set()
    while True:
        pool=[]
        for f in sorted(D.glob('common*.log')):
            for l in f.read_text().splitlines():
                if not l.startswith('NEAR '):continue
                r=l.split();p=tuple(map(int,r[2:]))
                if p in done:continue
                assert len(p)==193 and len(violations(p))==int(r[1])
                pool.append((int(r[1]),p))
        if not pool:break
        _,p=min(pool);done.add(p);finger=hashlib.sha256(b''.join(v.to_bytes(2,'big') for v in p)).hexdigest()
        for j,g in enumerate(gs):
            s,i,n,q=lift(p,g,int(sys.argv[1]),rng)
            print(json.dumps(dict(source=finger,partition=j,groups=g,status=s,vertices=q),separators=(',',':')),flush=True)
            if q:return
if __name__=='__main__':main()
