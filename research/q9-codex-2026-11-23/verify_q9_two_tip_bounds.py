"""Reconstruct master and face maxima with integer arithmetic, independently of the LP matrix."""
from itertools import combinations
from concurrent.futures import ProcessPoolExecutor
import json,random
from verify_q8_free_layer_dual import is_forest
from verify_q9_center_avoidance import verify,forms
from search_q9_two_tip_lift import build

def independent_upper(p,e,cert):
    verify(p);root=p[0];tips={root,p[-1]};A=set(range(256))-set(p[1:-1])
    factors=[tuple(1<<j for j in axes) for axes in cert["axes"]]
    weights={(m,v,z):w for m,v,z,w in cert["weights"]}
    fee=cert["end_weight"];balance=cert["balance_weight"];scale=cert["scale"]
    colour=lambda v:(v^root).bit_count()%2
    delta=sum(1 if not colour(v) else -1 for v in p)+(1 if e==0 else -1)
    assert abs(delta)<=2
    bound=2*fee+delta*balance;projections={}
    masks=[sum(f) for f in factors]
    for v in A:
        incident=[1<<j for j in range(8) if v^1<<j in A]
        choices=[]
        for d in range(3):
            total=d+int(v in tips)
            if total!=2 and not (total==1 and colour(v)==e):continue
            choices.extend(sum(bits) for bits in combinations(incident,d))
        values=[0] if v not in tips else []
        for z in choices:
            values.append(scale-(balance if not colour(v) else -balance)
                          -fee*int(z.bit_count()+int(v in tips)==1)
                          +sum(weights.get((m,v,z&m),0) for m in masks))
        bound+=max(values)
        for m in masks:projections[v,m]={z&m for z in choices}
    for axes,mask in zip(factors,masks):
        for base in range(256):
            if base&mask:continue
            cell=[v for v in A if v&~mask==base]
            if not cell:continue
            best=None
            for bits in range(1<<len(cell)):
                on={v for j,v in enumerate(cell) if bits>>j&1}
                if (tips&set(cell))-on:continue
                z={v:sum(d for d in axes if v^d in on) for v in on}
                if any(k not in projections[v,mask] for v,k in z.items()) or not is_forest(on,axes):continue
                value=-sum(weights.get((mask,v,k),0) for v,k in z.items())
                best=value if best is None else max(best,value)
            assert best is not None;bound+=best
    return bound

def compute(job):
    word,e=job;p=[0]
    for c in word:p.append(p[-1]^1<<int(c))
    axes=list(combinations(range(8),3));random.Random(314).shuffle(axes)
    const,scale,tables,cert=build(p,e,192,axes[:8])
    bound=independent_upper(p,e,cert)
    assert bound==const+sum(t[0][2] for _,t in tables)
    return [word,e,bound,193-len(p),cert]
if __name__=="__main__":
    words={}
    for f in ["q8_exchange_new_rooted_arms.txt","q8_exchange_second_rooted_arms.txt"]:
        for w in sorted(open(f).read().split(),key=lambda s:(-len(s),s)):
            p=[0]
            for c in w:p.append(p[-1]^1<<int(c))
            words.setdefault(forms(p,len(w))[0],w)
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(compute,((w,e) for w in words.values() for e in (0,1)),chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
