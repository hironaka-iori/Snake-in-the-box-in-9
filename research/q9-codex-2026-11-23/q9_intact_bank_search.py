"""Search an entire Q9 induced path with a specified mandatory ordered facet fragment."""
from pathlib import Path
from itertools import combinations
import json
import sys
from pysat.solvers import Minicard

def word_path(word):
    p=[0]
    for c in word:p.append(p[-1]^(1<<int(c)))
    return p

def verify(p):
    return len(p)==len(set(p)) and all(0<=x<512 for x in p) and all(((x^y).bit_count()==1)==(i==j+1) for i,x in enumerate(p) for j,y in enumerate(p[:i]))

def search(arm,goal,budget,hint=(),pins=(),validate_hint=True,majority_only=None,omit=(),forbid=(),exterior=None):
    assert verify(arm)
    fixed=set(arm)-set(omit)
    inside={v for v in fixed if sum(v^(1<<j) in fixed for j in range(9))==2}
    banned={v^(1<<i) for v in inside for i in range(9)}-fixed
    assert not (set(forbid)&fixed)
    pool=set(range(512))-banned-set(forbid)
    nbr={v:{v^(1<<i) for i in range(9)}&pool for v in pool}
    clauses=[];cards=[]
    def eq(values,need):
        values=list(values)
        if need<0 or need>len(values):
            clauses.append([]);return
        if need<len(values):cards.append((values,need))
        if need:cards.append(([-v for v in values],len(values)-need))
    if exterior is not None:
        seed_union, limit = exterior
        outside = [v+1 for v in sorted(pool-set(seed_union))]
        if limit < len(outside):cards.append((outside,limit))
    for v in fixed:clauses.append([v+1])
    # If v is selected, degree(v) plus its endpoint indicator is exactly two.
    for v,N in nbr.items():
        ep=513+v;clauses.append([-ep,v+1])
        var=[n+1 for n in N-fixed]+[ep];need=2-len(N&fixed)
        if need<0 or need>len(var):clauses.append([-v-1]);continue
        for ns in combinations(var,need+1):clauses.append([-v-1,*(-n for n in ns)])
        for ns in combinations(var,len(var)-need+1):clauses.append([-v-1,*ns])
    # Endpoints must be split by colour when goal is odd. When even, test
    # each possible majority class separately using ordinary assumptions.
    eq((513+v for v in pool),2)
    for i,j in combinations(range(9),2):
        a,b=1<<i,1<<j
        for v in pool:
            if v&(a|b):continue
            sq={v,v^a,v^b,v^a^b}
            if sq<=pool:clauses.append([-w-1 for w in sq-fixed])
    results=[]
    choices=(None,) if goal%2 else (0,1)
    if majority_only is not None:
        assert majority_only in choices
        choices=(majority_only,)
    for majority in choices:
        extra=len(cards);nc=len(clauses)
        for parity in (0,1):
            f={v for v in fixed if v.bit_count()%2==parity}
            free={v for v in pool-fixed if v.bit_count()%2==parity}
            n=(goal+1)//2+int(majority==parity)
            eq((v+1 for v in free),n-len(f))
            eq((v+513 for v in free|f),1 if majority is None else 2*int(majority==parity))
        with Minicard(bootstrap_with=clauses) as s:
            for lits,k in cards:s.add_atmost(lits,k)
            if hint:
                endpoints={v for v in hint if len(nbr[v]&set(hint))==1}
                literals=[v+1 if v in hint else -(v+1) for v in pool]+[v+513 if v in endpoints else -(v+513) for v in pool]
                assignment=set(literals)
                if validate_hint:
                    assert all(assignment.intersection(cl) for cl in clauses)
                    assert all(sum(v in assignment for v in ls)<=k for ls,k in cards)
                s.set_phases(literals)
            cuts=0;status="UNKNOWN";p=None
            while (left:=budget-s.accum_stats()["conflicts"])>0:
                s.conf_budget(left);sat=s.solve_limited(assumptions=[v+1 for v in pins])
                if sat is None:break
                if not sat:status="UNSAT";break
                model=set(s.get_model());selected={v for v in pool if v+1 in model}
                remaining=set(selected);path=None
                while remaining:
                    block=[remaining.pop()]
                    for x in block:
                        grow=nbr[x]&remaining;block.extend(grow);remaining-=grow
                    ends=[v for v in block if len(nbr[v]&selected)==1]
                    if not ends:
                        s.add_clause([-v-1 for v in block if v not in fixed]);cuts+=1
                    else:
                        assert len(ends)==2
                        connected=[ends[0]];last=-1
                        while len(connected)<len(block):
                            x=connected[-1];y,=nbr[x]&selected-{last};last=x;connected.append(y)
                        path=connected
                if path is not None and len(path)==goal+1:
                    assert fixed<=set(path) and verify(path)
                    status="FOUND";p=path;break
            results.append(dict(majority=majority,status=status,conflicts=s.accum_stats()["conflicts"],cuts=cuts,vertices=p))
        del cards[extra:];del clauses[nc:]
        if p:break
    return results

if __name__=="__main__":
    if sys.argv[1]=="control":
        p=json.loads(Path("q8_catalogue_lifts_verified.json").read_text())["lower_certificate"]["vertices"]
        assert verify(p)
        # Use an actual contiguous portion in a single facet, anchored in the real positive witness.
        runs=[];piece=[]
        for v in p:
            if piece and piece[-1]>>8!=v>>8:runs.append(piece);piece=[]
            piece.append(v)
        runs.append(piece);a=max(runs,key=len)
        for stride in (1,2,4,8):
            pins=[v for v in p[::stride] if v not in set(a)]
            rr=search(a,191,40000,set(p),pins)
            print(json.dumps(dict(mandatory=len(a),additional_pins=len(pins),stride=stride,r=rr)),flush=True)
    else:
        goal,cap,trim=map(int,sys.argv[1:4])
        bank=Path("q8_catalogue_96_98.words").read_text().split()
        for i in sorted(range(len(bank)),key=lambda j:(-len(bank[j]),j)):
            a=word_path(bank[i])
            if trim:a=a[trim:-trim]
            rr=search(a,goal,cap)
            print(json.dumps(dict(i=i,edges=len(a)-1,results=rr)),flush=True)
            if any(r["status"]=="FOUND" for r in rr):break
