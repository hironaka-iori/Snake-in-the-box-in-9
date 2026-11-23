"""Test every relative placement of two copies of one optimal Q8 snake.
Usage: python3 check_q8_multicross.py path/to/snake8_witness.json
"""
from pathlib import Path
import sys, json, itertools
p=json.loads(Path(sys.argv[1]).read_text())["vertex_sequence"]
assert len(p)==len(set(p))==99 and all(0<=x<256 for x in p)
assert all(((u^v).bit_count()==1)==(j==i+1) for i,u in enumerate(p) for j,v in enumerate(p) if i<j)
trans=[sum(1<<(x^t) for x in p) for t in range(256)]

from collections import Counter
counts=Counter()
def candidate(upper, k):
    vertices=set(p)|{256+x for x in upper}
    adj={v:{v^(1<<d) for d in range(9)}&vertices for v in vertices}
    def visit(removed):
        rest=vertices-removed
        fat=[(x,adj[x]-removed) for x in rest if len(adj[x]-removed)>2]
        if fat:
            if len(removed)==k or len(fat)>4*(k-len(removed)):return
            v,neighbors=fat[0]
            for q in {v}|neighbors:
                found=visit(removed|{q})
                if found:return found
        else:
            while rest:
                x=next(iter(rest)); cs={x}; stack=[x]
                while stack:
                    a=stack.pop()
                    for b in (adj[a]-removed)-cs: cs.add(b);stack.append(b)
                rest-=cs
                ends=[a for a in cs if len(adj[a]&cs)<=1]
                if len(cs)-(not ends)<198-k:continue
                if not ends:
                    a=next(iter(cs));cs.remove(a);ends=list(adj[a]&cs)
                path=[ends[0]]; used=set(path)
                while (opts:=(adj[path[-1]]&cs)-used):
                    q=next(iter(opts));path.append(q);used.add(q)
                assert len(set(path))==len(path) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(path) for j,b in enumerate(path) if j>i)
                return path
    return visit(set())
for perm in itertools.permutations(range(8)):
    lut=[0]*256
    for x in range(1,256):
        lo=x&-x
        lut[x]=lut[x^lo]|(1<<perm[lo.bit_length()-1])
    s=sum(1<<lut[x] for x in p)
    for t,a in enumerate(trans):
        m=(s&a).bit_count()
        # Deleting k vertices removes at most 3k edges. To reach 192, k <= 5.
        if m>11:continue
        counts[m]+=1
        w=candidate([lut[x]^t for x in p],5)
        if w:print("WITNESS",len(w)-1,w,flush=True);quit()
print("No 192-edge path. Exact placements searched after edge-count pruning:", sorted(counts.items()))
