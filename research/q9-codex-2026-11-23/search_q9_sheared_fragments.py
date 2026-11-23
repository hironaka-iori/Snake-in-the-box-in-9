"""Keep pieces of a sheared Q9 record path and allow arbitrary remaining vertices."""
from pathlib import Path
import collections, random, sys
from search_q9_anchored_sets import search
from itertools import combinations

def paircheck(p):
    assert len(set(p)) == len(p)
    assert all(((x ^ p[j]).bit_count() == 1) == (j == i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))

def run():
    sparse = "--sparse" in sys.argv
    totals = collections.Counter()
    seen = set()
    ds = [1<<d for d in range(9)]
    for row, word in enumerate(Path('q9_three_axis_191.in').read_text().split()):
        p = [0]
        for char in word:
            p.append(p[-1] ^ (1<<int(char)))
        paircheck(p)
        rng = random.Random(238309+row)
        if row == 0:
            fixed = set(rng.sample(p,155))
            status,w = search(fixed,set(p),191,25000,at_least=True)
            assert status == 'FOUND'
            paircheck(w)
            print('CONTROL',len(w)-1,flush=True)
        for axis in ds:
            for weight in (1,2,3,4,6,8):
                dirs = [v for v in ds if v!=axis]
                t = sum(rng.sample(dirs,weight))
                q = [v ^ t if v & axis else v for v in p]
                host = set(q)
                edges = {x:{x^d for d in ds} & host for x in host}
                if sparse and (row + axis.bit_length() + weight) % 3:continue
                for target_count in ((126,110,94) if sparse else (169,151)):
                    fixed = set(q)
                    adj = {x:z.copy() for x,z in edges.items()}
                    high = {x for x in fixed if len(adj[x])>2}
                    def drop(x):
                        for y in adj[x]:
                            adj[y].remove(x)
                            if len(adj[y])<=2:
                                high.discard(y)
                        adj[x].clear()
                        fixed.remove(x)
                        high.discard(x)
                    while high:
                        x = rng.choice(sorted(high))
                        c = {x}|adj[x]
                        v = max(sorted(c),key=lambda u:(int(u in high)+len(high & adj[u]),rng.random()))
                        drop(v)
                    while len(fixed)>target_count:
                        start=rng.randrange(len(q))
                        for x in q[start:start+rng.randint(2,8)]:
                            if x in fixed:drop(x)
                            if len(fixed)<=target_count:break
                    key = sum(1<<x for x in fixed)
                    if key in seen:continue
                    seen.add(key)
                    status,w = search(fixed,host,192,700,at_least=True)
                    totals[status]+=1
                    if status == 'UNKNOWN':
                        print('UNRESOLVED',hex(key),hex(sum(1<<x for x in host)),flush=True)
                    if w:
                        paircheck(w); assert len(w)>=193 and fixed<=set(w)
                        print('FOUND',len(w)-1,*w,flush=True);return
        print('ROW',row,dict(totals),flush=True)
    print('DONE',dict(totals),flush=True)
if __name__ == '__main__':run()
