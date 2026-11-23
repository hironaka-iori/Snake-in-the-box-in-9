from common import solver
from anywhere import *
from runs import select,sizes,bad
import random
def cross(n,seed):
    rng=random.Random(seed);bank=corpus(n);items=bank[:min(350,len(bank))]
    with (D/f'cross{n}.jsonl').open('w') as f:
        for j in range(1800):
            error,name,ix,w=items[j%len(items)];ws=select(n,bad(vertices(w)),rng,rng.randrange(3,9));ds=list(range(9));rng.shuffle(ds);p=[ds[j:j+2] for j in (0,2,4,6)];lens=sizes(n,ws)
            st,path,c=solver.solve(w,p,ds[8],lens,20000);row=dict(source=name,id=ix,w=''.join(map(str,w)),spans=ws,pairs=p,single=ds[8],status=st,conflicts=c)
            if path:
                from common import check
                check(w,p,ds[8],lens,path);row['path']=path
            print(json.dumps(row,separators=(',',':')),file=f,flush=True)
            if path:break
if __name__=='__main__':cross(*map(int,sys.argv[1:]))
