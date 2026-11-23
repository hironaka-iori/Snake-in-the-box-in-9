"""Exact subpattern matching up to all coordinate permutations and XOR translations."""
import json
from pathlib import Path
from collections import Counter
from q9_overlapping_port_bound import ROOT,NEIGH,controls

def edges_within(S):
    return {(v,w) for v in S for w in NEIGH[v] if w in S and v<w}

def axis(edge):
    return (edge[0]^edge[1]).bit_length()-1

def contained(needle, required):
    pat={v for e in needle for v in e}
    pe=edges_within(pat); te=edges_within(required)
    pc=Counter(map(axis,pe));tc=Counter(map(axis,te))
    if any(x>y for x,y in zip(sorted(pc.values(),reverse=True)+[0]*9,sorted(tc.values(),reverse=True)+[0]*9)):return False
    anchor=max(pat,key=lambda v:sum(w in pat for w in NEIGH[v]))
    rel=[v^anchor for v in pat]
    def signatures(points):
        return [Counter(x.bit_count() for x in points if x>>d&1) for d in range(9)]
    source=signatures(rel)
    sd=Counter(x.bit_count() for x in rel)
    for dest in required:
        rr={v^dest for v in required}
        if not sd<=Counter(x.bit_count() for x in rr):continue
        target=signatures(rr)
        options=[[j for j in range(9) if pc[i]<=tc[j] and source[i]<=target[j]] for i in range(9)]
        order=sorted(range(9),key=lambda d:len(options[d]))
        pp=[-1]*9
        def extend(k,used):
            if k==9:return all(sum(((v>>d)&1)<<pp[d] for d in range(9)) in rr for v in rel)
            d=order[k]
            for j in options[d]:
                if not used>>j&1:
                    pp[d]=j
                    if extend(k+1,used|1<<j):return True
            return False
        if extend(0,0):return True
    return False

def patterns():
    return [json.loads((ROOT/f).read_text())["required_edges"] for f in
            ("q9_positive_ports_220_certificate.json","q9_positive_ports_balanced_certificate.json")]

if __name__=="__main__":
    ps=patterns()
    for p in ps:
        test={511^int(f"{v:09b}"[::-1],2) for e in p for v in e}
        assert contained(p,test)
    for i,es in enumerate(controls()):
        req={v for e in es for v in e}
        print(i,*[int(contained(p,req)) for p in ps])
