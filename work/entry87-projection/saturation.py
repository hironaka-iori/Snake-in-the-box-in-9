"""Necessary constraints on a saturated same-parity set of 32 intervals."""
import json
from pathlib import Path
from fractions import Fraction
from solve import paths, save
from exact_cover import components_partition


def separation(a,b):
    return min((x^y).bit_count() for x in a for y in b)


def signs(path,trace):
    # For opposite parity words, distance one between free words makes the
    # entire vertices adjacent precisely at retained distance zero.
    index=0
    at=[]
    for t in trace:
        at.append(list(range(index,index+len(t))))
        index+=len(t)
    out={}
    for a,t in enumerate(trace):
        for b in range(a+1,len(trace),2):
            repeated=[(i,j) for i,x in zip(at[a],t) for j,y in zip(at[b],trace[b]) if x==y]
            must=b==a+1
            forbid=any(j>i+1 for i,j in repeated)
            out[a,b]=out[b,a]=(must,forbid)
    return out


def analyze(target,row,p,profile):
    trace=components_partition(target,row["bits"])
    lookup={tuple(t["trace"]):Fraction(t["weight"]) for t in profile["weights"]}
    A=[r for r in range(p,len(trace),2) if lookup.get(tuple(sorted(trace[r])),0)==1]
    assert len(A)==32
    assert all(separation(trace[a],trace[b])<=1 for i,a in enumerate(A) for b in A[i+1:])
    B=list(range(1-p,len(trace),2))
    opposite=signs(target,trace)
    rooms=[dict(r=b,possible=[a for a in A if not opposite[a,b][1]],
                required=[a for a in A if opposite[a,b][0]]) for b in B]
    for room in rooms:
        assert set(room["required"])<=set(room["possible"])
    # Identifying same-parity colors intersects their possible 6-element
    # neighborhoods; different colors have at most two common neighbors.
    forbidden_equal=[]
    forced_equal=[]
    unknown=[]
    for j,b in enumerate(B):
        for i,a in enumerate(B[:j]):
            x,y=rooms[i],rooms[j]
            P=set(x["possible"])&set(y["possible"])
            R=set(x["required"])&set(y["required"])
            U=set(x["required"])|set(y["required"])
            cannot_share=separation(trace[a],trace[b])<=1 or len(P)<6 or not U<=P
            must_share=len(R)>2
            if cannot_share: forbidden_equal.append((a,b))
            if must_share: forced_equal.append((a,b))
            if not cannot_share and not must_share: unknown.append((a,b))
    # Maximize a clique exactly on the pairwise incompatibility graph.
    # Distinct complement-parity words also have only 32 possible labels.
    graph={x:set() for x in B}
    for a,b in forbidden_equal:
        graph[a].add(b)
        graph[b].add(a)
    import networkx as nx
    G=nx.Graph(graph)
    clique=max(nx.find_cliques(G),key=len)
    return dict(bits=row["bits"],saturated_parity=p,anchors=A,rooms=rooms,
                min_room=min(len(r["possible"]) for r in rooms),
                same_word_forbidden=len(forbidden_equal),same_word_forced=forced_equal,
                opposite_clique=sorted(clique))


if __name__=="__main__":
    _,q=paths()
    rows=json.loads(Path("color-duals.json").read_text())
    result=[analyze(q,row,p,profile) for row in rows for p,profile in enumerate(row["parities"])
            if Fraction(profile["value"])==32]
    save(Path("saturation.json"),result)
    for r in result:
        print(r["bits"],r["min_room"],len(r["opposite_clique"]),r["same_word_forced"])
