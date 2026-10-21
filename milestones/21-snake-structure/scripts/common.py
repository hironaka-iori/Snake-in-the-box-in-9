import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
import json
BANK=_os.path.join(REPO, 'work', 'bank9.json')
def load():
    return json.load(open(BANK))
def pc(x): return bin(x).count('1')
def is_snake(vs):
    S=set(vs)
    if len(S)!=len(vs): return False
    pos={v:i for i,v in enumerate(vs)}
    for i,v in enumerate(vs):
        if i and pc(v^vs[i-1])!=1: return False
        d=0
        while (1<<d)<= max(max(vs),1)*2:
            u=v^(1<<d)
            if u in pos and abs(pos[u]-i)>1: return False
            d+=1
    return True
def is_snake_n(vs,n):
    pos={}
    for i,v in enumerate(vs):
        if v in pos: return False
        pos[v]=i
    for i,v in enumerate(vs):
        if i and pc(v^vs[i-1])!=1: return False
        for d in range(n):
            j=pos.get(v^(1<<d))
            if j is not None and abs(j-i)>1: return False
    return True
def light(e,k):
    cc={int(a):b for a,b in e['coordinate_counts'].items()}
    return sorted(cc,key=lambda c:cc[c])[:k]
