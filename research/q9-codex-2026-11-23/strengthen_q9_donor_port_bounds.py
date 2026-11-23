"""Strengthen port-branch bounds which still admit 192, preserving integer duals."""
import gzip,json,random,sys
from itertools import combinations
from pathlib import Path
from split_q9_long_donor_ports import path
from stream_q9_port_branches import rows
def strong(record):
    from certify_q9_intact_q8_facet import build
    i,r,count,seed=record;p=path(r['word']);low=set(p)|set(r['added'])
    a=list(combinations(range(8),4));random.Random(seed).shuffle(a)
    b=list(combinations(range(8),3));random.Random(403215).shuffle(b)
    x=build(p,r['ports'],low,r['ends'],r['delta'],b[:10]+a[:count])
    if x is None:return [i,dict(word=r['word'],added=r['added'],ports=r['ports'],full=r['full'],empty=True)]
    const,scale,t,c=x
    u=const+sum(f[0][2] for _,f in t);m=len(low)-1+u//scale;m-=int(m%2!=r['full'][0]%2)
    return [i,{**r,'bound':m,'numerator':u,'cert':c}]
if __name__=='__main__':
    from concurrent.futures import ProcessPoolExecutor
    src,dest,count,seed,workers=sys.argv[1:6]
    with ProcessPoolExecutor(int(workers)) as pool,gzip.open(dest,'wt') as out:
        batch=[];limit=int(workers)*3
        for i,r in enumerate(rows(src)):
            if r.get('bound',0)<192:continue
            batch.append(pool.submit(strong,(i,r,int(count),int(seed))))
            while len(batch)>=limit or (batch and batch[0].done()):
                j,z=batch.pop(0).result();print(j,z.get('bound','EMPTY'),flush=True)
                out.write(json.dumps([j,z],separators=(',',':'))+'\n');out.flush()
        for f in batch:
            j,z=f.result();print(j,z.get('bound','EMPTY'),flush=True)
            out.write(json.dumps([j,z],separators=(',',':'))+'\n');out.flush()
    print('DONE',flush=True)
