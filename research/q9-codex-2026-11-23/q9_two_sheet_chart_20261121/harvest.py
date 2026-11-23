from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent;R=D.parent
def canon(s):
    def one(v):
        d={};return tuple(d.setdefault(x,len(d)) for x in v)
    return min(one(s),one(s[::-1]))
def valid(p,n):
    used=set()
    for i,x in enumerate(p):
        assert 0<=x<1<<n and x not in used and {x^(1<<k) for k in range(n)}&used==({p[i-1]} if i else set())
        used.add(x)
def ordered(z):
    v=0;p=[v]
    for c in z:v^=1<<c;p.append(v)
    return p
def load(f):
    for i,s in enumerate(f.read_text().splitlines()):
        n,*p=map(int,s.split());valid(p,n);yield i,n,p,[(x^y).bit_length()-1 for x,y in zip(p,p[1:])]
def main():
    d={};N=Counter()
    for i,n,p,w in load(R/'q9_three_seam_folds/q10_12.txt'):d[canon(w)]=None
    known=set(d);out=[]
    for name in ('donors.txt','donors12.txt','donors13.txt'):
        for i,n,p,w in load(R/'q9_via_q10'/name):
            if n<=10:continue
            c=Counter();h=0
            for l,x in enumerate(w):
                while h<len(w) and (len(c)<10 or w[h] in c):c[w[h]]+=1;h+=1
                if h-l>=191 and len(c)==10 and (l==0 or w[l-1] not in c):
                    key=canon(w[l:h]);N[n]+=1
                    if key not in d:
                        ex=dict(file=name,row=i,dim=n,start=l,stop=h);d[key]=ex;out.append((key,ex))
                c[x]-=1
                if not c[x]:del c[x]
    with (D/'subfacets.pts').open('w') as f:
        for a,s in out:print(10,*ordered(a),file=f)
    (D/'subfacets.json').write_text(json.dumps([s for a,s in out],separators=(',',':'))+'\n')
    print("maximal_source_windows",dict(N),"new_Q10_shapes",len(out),"lengths",sorted(Counter(map(lambda z:len(z[0]),out)).items()),"source_dimensions",dict(Counter(s['dim'] for _,s in out)))
if __name__=='__main__':main()
