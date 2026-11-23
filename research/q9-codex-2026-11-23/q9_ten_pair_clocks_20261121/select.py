from collections import defaultdict
from pathlib import Path
import json
D=Path(__file__).resolve().parent
def key(w):
    def norm(s):
        m={};return ''.join('4' if c=='4' else m.setdefault(c,str(len(m))) for c in s)
    return min(norm(w),norm(w[::-1]))
def readranges(s):
    for pair in s.rstrip(',').split(','):
        a,b=map(int,pair.split('-'));yield from range(a,b+1)
def select(g,src):
    inp=D/f'all{g}.logtmp';d={};witnesses=defaultdict(list);count=0
    for line in inp.open():
        row,ix,mp,w,rr=line.split();row=int(row);ix=int(ix);last=len(w)-g
        ss=sorted(set([0,1,last,last-1,last//2]+[(last*x)//4 for x in (1,3)]))
        for start in sorted(set(readranges(rr))&set(ss)):
            raw=w[start:start+g];group=''.join(str(int(x)//2) for x in raw);canon=key(group);count+=1
            if canon not in d:d[canon]=len(d);witnesses[canon].append((row,start,ix,mp,raw,group))
    with (D/f'{src}{g}.tsv').open('w') as out:
        for word,j in d.items():
            row,start,ix,mp,raw,group=witnesses[word][0];print(row,start,ix,mp,-1,group,raw,file=out)
    return dict(target=g,raw_instances=count,canonical_survivors=len(d),total=12*7*4725)
if __name__=='__main__':print(json.dumps([select(g,'priority') for g in (192,195,196)]))
