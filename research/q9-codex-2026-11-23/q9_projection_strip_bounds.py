"""Exact Q4 strip bounds for lifts of Q6 walks with three free coordinates."""
from collections import defaultdict
from functools import lru_cache
import json,sys

def pattern(mask):
    rest={v for v in range(16) if mask>>v&1}
    nb={v:[v^(1<<i) for i in range(4) if v^(1<<i) in rest] for v in rest}
    if any(len(n)>2 for n in nb.values()):return None
    words=[]
    for start in [v for v in rest if len(nb[v])<=1]:
        if start not in rest:continue
        cur=start;word=[]
        while True:
            rest.remove(cur)
            if not word or word[-1]!=cur>>3:word.append(cur>>3)
            ns=[v for v in nb[cur] if v in rest]
            if not ns:break
            cur=ns[0]
        w=tuple(word);words.append(min(w,w[::-1]))
    return None if rest else tuple(sorted(words))

@lru_cache(maxsize=1)
def catalogue():
    out=defaultdict(list)
    for m in range(65536):
        k=pattern(m)
        if k is not None:out[k].append(m)
    return out

def signatures(p):
    pos=[[] for _ in range(64)]
    for i,v in enumerate(p):pos[v].append(i)
    for u in range(64):
        for d in range(6):
            v=u^(1<<d)
            if v<u:continue
            ids=sorted(pos[u]+pos[v]);words=[];w=()
            for j,i in enumerate(ids):
                if j and i!=ids[j-1]+1:words.append(min(w,w[::-1]));w=()
                w+=(int(p[i]==v),)
            if w:words.append(min(w,w[::-1]))
            yield u,v,d,tuple(sorted(words))

@lru_cache(maxsize=None)
def upper(sig):
    rows=catalogue().get(sig,[])
    if not rows:return (-1,-1,-1)
    be=sum(1<<i for i in range(16) if i.bit_count()%2==0)
    return max(m.bit_count() for m in rows),max((m&be).bit_count() for m in rows),max((m&~be).bit_count() for m in rows)

def bounds(p):
    totals=[[0,0,0] for _ in range(6)]
    for u,v,d,s in signatures(p):
        n,a,b=upper(s)
        if n<0:return (0,0,0)
        if u.bit_count()%2:a,b=b,a
        for j,x in enumerate((n,a,b)):totals[d][j]+=x
    return tuple(min(t[j] for t in totals) for j in range(3))

if __name__=='__main__':
    for row in map(json.loads,open(sys.argv[1])):
        if row[0]=="UNKNOWN":
            print(json.dumps([row[1],*bounds(bytes.fromhex(row[1]))]),flush=True)
