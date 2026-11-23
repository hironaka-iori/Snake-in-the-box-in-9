"""Join independently reordered Q8 arms with prescribed even vertices in each layer."""
from itertools import combinations
from collections import Counter, defaultdict
from functools import lru_cache
import argparse
from pysat.solvers import Minicard
from search_q9_wynn_plateau import verify

def chain(code):
    p = [0]
    for c in code:
        p.append(p[-1] ^ (1 << int(c)))
    return p

def mask(items):
    return sum(1 << i for i in items)

ODDS = [i for i in range(256) if i.bit_count() % 2]
EVENS = [i for i in range(256) if not i.bit_count() % 2]
NBR = {w: mask(w ^ (1 << d) for d in range(8)) for w in range(256)}

def bits(x):
    while x:
        bit = x & -x
        yield bit.bit_length() - 1
        x -= bit

@lru_cache(maxsize=60000)
def partners(chosen, odd_end, limit):
    ev = list(bits(chosen))
    slots = {v: [] for v in ev}
    ends = []
    for w in ODDS:
        touched = chosen & NBR[w]
        n = touched.bit_count()
        if n != 2 and not (odd_end and n == 1 and touched != 1):
            continue
        for v in bits(touched):
            slots[v].append(w+1)
        if n==1:
            ends.append(w+1)
    if not slots[0] or any(not a for a in slots.values()):
        return (), False
    forced_tips = sum(len(a)==1 for v,a in slots.items() if v)
    if forced_tips > 1-int(odd_end) or (odd_end and not ends):
        return (), False
    if not odd_end:
        for v in ev[1:]:
            ends.append(v+257)
            slots[v].append(v+257)
    results = []
    with Minicard() as sat:
        def exact(a,n):
            if len(a)<n:
                sat.add_clause([])
            else:
                sat.add_atmost(a,n)
                sat.add_atmost([-v for v in a],len(a)-n)
        exact(ends,1)
        for v,a in slots.items():
            exact(a,2 if v else 1)
        while sat.solve():
            model = set(sat.get_model())
            om = mask(w for w in ODDS if w+1 in model and
                      any(w+1 in slots[v] for v in bits(chosen & NBR[w])))
            full = chosen | om
            path = [0]
            seen = 1
            while adj := NBR[path[-1]] & full & ~seen:
                assert adj.bit_count()==1
                v = adj.bit_length()-1
                path.append(v)
                seen |= adj
            if full == seen:
                assert verify(path)
                results.append((om,bytes(path)))
                if len(results)>=limit:
                    return tuple(results), True
            # Every connector choice has a fixed cardinality for this parity.
            sat.add_clause([-(w+1) for w in bits(om)])
    return tuple(results), False

def variants(base, n_edits):
    yield base
    for x in EVENS[1:]:
        yield base ^ (1<<x)
    if n_edits>=2:
        for x in bits(base & ~1):
            for y in EVENS[1:]:
                if not base>>y & 1:
                    yield base ^ (1<<x) ^ (1<<y)

def arm_pairs(path):
    rows=set()
    for line in open(path):
        _,*steps=map(int,line.split())
        for d in set(steps):
            if steps.count(d)!=1:continue
            i=steps.index(d)
            first,second=sorted((steps[:i][::-1],steps[i+1:]),key=len)
            conv={}
            def norm(s):
                return ''.join(str(conv.setdefault(j,len(conv))) for j in s)
            rows.add((norm(first),norm(second)))
    return sorted(rows)

def run(pair,goal,edits,limit):
    stats=Counter()
    banks=[defaultdict(list),defaultdict(list)]
    for bank,s in zip(banks,pair):
        a=chain(s)
        assert verify(a)
        base=mask(v for v in a if v.bit_count()%2==0)
        for c in (variants(base,edits) if edits else [base]):
            for odd_end in (False,True):
                length=2*c.bit_count()-2+int(odd_end)
                if not goal-99<=length<=98:continue
                stats['sets']+=1
                paths,clipped=partners(c,odd_end,limit)
                stats['clipped']+=clipped
                stats['paths']+=len(paths)
                bank[length].extend((c,om,p) for om,p in paths)
    for l,left in banks[0].items():
        right=banks[1][goal-1-l]
        for a,oa,pa in left:
            stats['pairs']+=len(right)
            for b,ob,pb in right:
                if a&b==1 and not oa&ob:
                    full=list(pa[::-1])+[256+v for v in pb]
                    assert len(full)==goal+1 and verify(full)
                    return stats,full
    return stats,None

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('records')
    ap.add_argument('--goal',type=int,default=192)
    ap.add_argument('--edits',type=int,choices=(0,1,2),default=1)
    ap.add_argument('--limit',type=int,default=1000)
    ap.add_argument('--start',type=int,default=0)
    ap.add_argument('--stop',type=int,default=None)
    args=ap.parse_args()
    for i,p in enumerate(arm_pairs(args.records)[args.start:args.stop],args.start):
        stats,found=run(p,args.goal,args.edits,args.limit)
        print(i,dict(stats),'FOUND' if found else 'END',found or '',flush=True)
