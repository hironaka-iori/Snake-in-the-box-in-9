"""Exact one-axis lifts of projected simple paths, with optional other-coordinate transpositions."""
import argparse,json
from collections import Counter
from itertools import combinations
from math import comb
from pathlib import Path
from solve import BANK,BANK_HASH,sha256,defects,save


def project(path,axis):
    bit=1<<axis;P=[];sw=[]
    for v in path:
        x=(v&(bit-1))|((v>>(axis+1))<<axis)
        if P and x==P[-1]:sw.append(len(P)-1)
        else:P.append(x)
    assert len(P)==len(set(P)) and len(set(sw))==len(sw)
    return P,sw


def literal(P,positions):
    q=[];layer=0
    for i,v in enumerate(P):
        q.append(v|(layer<<8))
        if i in positions:
            layer^=1;q.append(v|(layer<<8))
    return q


def setup(P):
    idx={v:i for i,v in enumerate(P)}
    if len(idx)!=len(P) or any((a^b).bit_count()!=1 for a,b in zip(P,P[1:])):return None
    forbidden=set();chords=[]
    for i,x in enumerate(P):
        for b in range(8):
            j=idx.get(x^(1<<b),-1)
            if j>i+1:
                forbidden.add(i);forbidden.add(j);chords.append((i,j))
    eligible=[i for i in range(len(P)) if i not in forbidden]
    return eligible,chords


def linear(rows):
    pivots={}
    for m,z in rows:
        while m:
            bit=m.bit_length()-1
            if bit not in pivots:
                pivots[bit]=(m,z);break
            a,b=pivots[bit];m^=a;z^=b
        if not m and z:return None
    return pivots


def solve(P,target,all_sol=True):
    geom=setup(P)
    if geom is None:return dict(reason="repeated or nonadjacent trace")
    E,chords=geom
    if target>len(E) and not all_sol:return dict(reason="too few available crossings",available=len(E))
    rows=[(sum(1<<i for i,v in enumerate(E) if a<v<b),1) for a,b in chords]
    piv=linear(rows)
    if piv is None:return dict(reason="inconsistent parity equations",available=len(E))
    bits=[i for i in range(len(E)) if i not in piv]
    # Each free assignment uniquely completes the triangular pivot equations.
    # Consecutive base positions cannot both cross: the four vertices would
    # fill a square. Chord endpoints never belong to E.
    blocked=[((1<<i)|(1<<(i+1))) for i in range(len(E)-1) if E[i+1]==E[i]+1]
    profile=Counter();example=None
    for f in range(1<<len(bits)):
        assignment=sum(((f>>j)&1)<<v for j,v in enumerate(bits))
        for j,(m,z) in sorted(piv.items()):
            value=z^((m&assignment).bit_count()%2)
            assignment|=value<<j
        if any(assignment&mask==mask for mask in blocked):continue
        weight=assignment.bit_count();profile[weight]+=1
        if weight==target:
            sites=[v for i,v in enumerate(E) if assignment>>i&1]
            example=literal(P,set(sites))
            assert len(example)==len(P)+target and not defects(example)
            if not all_sol:break
    return dict(reason="complete affine census",available=len(E),rank=len(piv),nullity=len(bits),
                profile=profile,witness=example)


def check_literal():
    for P in ([0,1,3,2],[0,1,3,7,6,2],[0,1,3,7],[0,1,3,2,6,7]):
        brute=Counter()
        for m in range(1<<len(P)):
            sites={i for i in range(len(P)) if m>>i&1}
            if not defects(literal(P,sites)):brute[len(sites)]+=1
        out=solve(P,0,True)
        assert Counter(out.get("profile",{}))==brute


def run(a):
    check_literal()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    qs=json.loads(raw);result=[];found=None
    for index in range(a.start,a.stop):
        q=qs[index]["vertex_sequence"]
        for axis in range(9):
            P,original=project(q,axis);k=193-len(P)
            if not a.transpose:
                positive=literal(P,set(original));assert len(positive)==192 and not defects(positive)
                row=solve(P,k)
                assert row.get("profile",{}).get(len(original),0)>0 or row.get("reason")=="too few available crossings"
                result.append(dict(entry=index,axis=axis,target=k,**row))
                if row.get("witness"):found=row["witness"];break
            else:
                base=set(P);stats=Counter();changes=0;best=-1
                for j in range(1,len(P)-1):
                    alternative=P[j-1]^P[j]^P[j+1]
                    if alternative in base:continue
                    Q=P.copy();Q[j]=alternative;changes+=1
                    row=solve(Q,k,False);stats[row["reason"]]+=1
                    if row.get("profile"):best=max(best,max(row["profile"]))
                    if row.get("witness"):
                        found=row["witness"];break
                result.append(dict(entry=index,axis=axis,target=k,squares=changes,counts=stats,
                                   max_returned_switches=best,witness=found))
                if found:break
        if found:break
    tag="square" if a.transpose else "fixed"
    save(Path(f"punctured-{tag}-{a.start}-{a.stop}.json"),result)
    print(tag,len(result),sum(bool(r.get("witness")) for r in result),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--transpose",action="store_true");run(p.parse_args())
