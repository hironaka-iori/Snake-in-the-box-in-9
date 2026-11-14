"""Independent two-coordinate classification for weights through 20 in the ten-cube parity model."""
import argparse
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from second_weight import neighbours,mask
from solve import save


def supports(s):
    while s:
        low=s&-s;yield low.bit_length()-1;s^=low


def sections(domain,target,parity,budget,balls):
    # D(lower section) must equal the other discrepancy. Each address in the
    # lower section but outside its own discrepancy consumes a doubled fibre.
    allowed=list(supports(domain))
    outside=[v for v in range(256) if v.bit_count()%2==parity and not (domain>>v&1)]
    lookup={0:(0,0)}
    for k in range(1,budget+1):
        for choices in combinations(outside,k):
            syndrome=0
            for v in choices:syndrome^=balls[v]
            assert syndrome not in lookup
            lookup[syndrome]=(k,mask(choices))
    out=[];s=signature=0
    for step in range(1<<len(allowed)):
        if step:
            v=allowed[(step&-step).bit_length()-1]
            s^=1<<v;signature^=balls[v]
        if (matched:=lookup.get(signature^target)) is not None:
            k,extra=matched;out.append((k,s^extra))
    return out


def pair_type(s,t):
    def types(x,y):return tuple(sorted(((x>>i)&1,(y>>i)&1) for i in range(8)))
    return min(types(s,t),types(t,s))


if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--weight",type=int,choices=(20,22),default=20)
    bound=parser.parse_args().weight
    n8=[mask(neighbours(v,8)) for v in range(256)]
    n10=[mask(neighbours(v,10)) for v in range(1024)]
    pairs={}
    for s,t in combinations((v for v in range(1024) if v.bit_count()%2),2):
        word=n10[s]^n10[t];assert word not in pairs;pairs[word]=(s,t)
    # A translation normalizes the centre of the eight-site odd discrepancy
    # to zero. A translation that also changes one deleted bit can exchange
    # the roles of the two residual parities.
    cases=[(n8[(1<<k)-1],n8[0],f"8+8 distance {k}") for k in (1,3,5,7)]
    types={}
    for s,t in combinations((v for v in range(256) if v.bit_count()%2),2):
        if (s^t).bit_count()==2:types.setdefault(pair_type(s,t),(s,t))
    for s,t in types.values():cases.append((n8[s]^n8[t],n8[0],f"12+8 pair {s},{t}"))
    rows=[]
    for even,odd,name in cases:
        budget=(bound-even.bit_count()-odd.bit_count())//2
        left=sections(even,odd,0,budget,n8);right=sections(odd,even,1,budget,n8)
        weights=Counter()
        for (i,a),(j,b) in product(left,right):
            if i+j>budget:continue
            whole=a|(b<<256)|((b^odd)<<512)|((a^even)<<768)
            check=0
            for v in supports(whole):check^=n10[v]
            assert check==0 and whole.bit_count()==even.bit_count()+odd.bit_count()+2*(i+j)
            if whole.bit_count()<=20:assert whole in pairs
            else:
                triples=[]
                for centre in range(1024):
                    if centre.bit_count()%2 and (p:=pairs.get(whole^n10[centre])) and centre<p[0]:
                        triples.append((centre,*p))
                assert len(triples)==1 and sum((u^v).bit_count()==2 for u,v in combinations(triples[0],2))>=2
            weights[whole.bit_count()]+=1
        rows.append(dict(configuration=name,complete_lifts=weights))
    path="low-weight-lifts.json" if bound==20 else f"low-weight-lifts-{bound}.json"
    save(Path(path),rows)
    print(len(rows),[(r["configuration"],dict(r["complete_lifts"])) for r in rows if r["complete_lifts"]])
