from collections import Counter
from pathlib import Path
import json
D=Path(__file__).resolve().parent;R=D.parent
def canon(w):
    def n(s):
        return ''.join(str(v) for v in [*map(list(dict.fromkeys(s)).index,s)])
    return min(n(w),n(w[::-1]))
def walk(w):
    p=[0]
    for k in w:p.append(p[-1]^1<<int(k))
    return p
def valid(p):
    return len(set(p))==len(p) and all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def main():
    bank={}
    for i,w in enumerate((R/'q8_single_cross_complete_arms.txt').read_text().split()):
        bank.setdefault(canon(w),('rooted',i,w))
    donors=(R/'q8_catalogue_96_98.words').read_text().split()
    for i,w in enumerate(donors):
        for trim in range(4):
            for a in range(trim+1):
                frag=w[a:len(w)-(trim-a)]
                if len(frag)>=93:bank.setdefault(canon(frag),('catalogue',i,w,a,trim-a))
    by=Counter();hits=Counter();cases=[]
    for w,src in sorted(bank.items(),key=lambda z:(-len(z[0]),z[0])):
        p=walk(w);by[src[0],len(w)]+=1
        forbidden=set(p)|{z^1<<k for z in p for k in range(8)}
        free=set(range(256))-forbidden
        edges=sorted({tuple(sorted((x,y))) for x in free for y in (x^1<<k for k in range(8)) if y in free})
        if edges:
            hits[src[0],len(w)]+=1
            assert valid(p)
            for u,v in edges:
                assert all((x^y).bit_count()>=2 for x in (u,v) for y in p)
                assert all(sum((x^y).bit_count()==1 for y in (u,v,u+256,v+256))==2 for x in (u,v,u+256,v+256))
                cases.append(dict(w=w,lo=p,edge=(u,v),source=src))
    (D/'cases.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in cases))
    with (D/'cases.dat').open('w') as f:
        for c in cases:print(c['w'],*c['edge'],file=f)
    print('tested',sorted(by.items()),'hits',sorted(hits.items()),'edge_cases',Counter((c['source'][0],len(c['w'])) for c in cases))
if __name__=='__main__':main()
