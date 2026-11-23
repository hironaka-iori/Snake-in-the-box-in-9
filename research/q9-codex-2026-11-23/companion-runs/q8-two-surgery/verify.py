"""Check both induced paths and every cross pair; canonicalize their joint placement."""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse,json

def parse(line):
    x=list(map(int,line.split()));paths=[]
    while x:
        n=x[0];assert n>=1 and len(x)>n;paths.append(x[1:n+1]);x=x[n+1:]
    return paths

def shape(p):
    keys=[]
    for a,b in [p,p[::-1]]:
        for u,v in product((a,a[::-1]),(b,b[::-1])):
            m={};steps=[]
            for w in (u,v):
                steps.append(tuple(m.setdefault(x^y,len(m)) for x,y in zip(w,w[1:])))
            offset=u[0]^v[0];mapped=sum((1<<d) for x,d in m.items() if offset&x);unused=(offset&~sum(m)).bit_count()
            keys.append((*steps,mapped,unused))
    return min(keys)

def valid(paths):
    assert len(paths)==2 and len({x for p in paths for x in p})==sum(map(len,paths))
    assert all(0<=x<256 for p in paths for x in p)
    for p in paths:assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p) if j>i)
    assert all((x^y).bit_count()>=2 for x in paths[0] for y in paths[1])
def main():
    r=Path(__file__).resolve().parent
    import sys
    files=[Path(x) for x in sys.argv[1:]];raw=Counter();baselines=set();known={};src={}
    for f in files:
        for l in f.read_text().splitlines():
            p=parse(l)
            if len(p)!=2:continue
            valid(p); k=shape(p)
            if f.name.startswith('baseline'):baselines.add(k);continue
            if sum(map(len,p))<100:continue
            raw[f.name]+=1
            if k not in known:known[k]=p;src[k]=f.name
    def save(target,subset):
        lines=[]
        for k in subset:
            p=known[k];zero=p[0][0];lines.append(' '.join(' '.join(map(str,[len(w),*(x^zero for x in w)])) for w in p))
        (r/target).write_text('\n'.join(lines)+('\n' if lines else ''))
    order=sorted(known,key=lambda k:(-sum(map(len,known[k])),tuple(sorted(map(len,known[k]))),k))
    save('ready.pts',order);save('beyond_baseline.pts',[k for k in order if k not in baselines])
    summary=dict(rows=raw,unique=len(order),unique_by_sizes=dict(Counter('+'.join(map(str,sorted(map(len,p)))) for p in known.values())),compared_baseline=len(baselines),beyond_comparison=sum(k not in baselines for k in order))
    (r/'verified.json').write_text(json.dumps(summary,indent=1)+'\n');print(summary)
if __name__=='__main__':main()
