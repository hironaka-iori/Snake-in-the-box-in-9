"""An LP relaxation using path lags, Hamming spectra, and Q4 forest counts."""

import argparse
from collections import Counter
import gzip
from functools import lru_cache
from itertools import combinations
import json
from math import comb, cos, pi
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from q9_q4_forest_diagram import forest_masks


def krawtchouk(distance, order):
    return sum((-1)**i*comb(distance,i)*comb(9-distance,order-i)
               for i in range(max(0,order+distance-9),min(order,distance)+1))


def local_signatures(windows=False):
    result = set()
    for mask in forest_masks():
        selected = [v for v in range(16) if mask>>v&1]
        spectrum = Counter((u^v).bit_count() for u,v in combinations(selected,2))
        inner = sum(sum((vertex^(1<<i)) in selected for i in range(4))==2
                    for vertex in selected)
        exterior = [sum((v^(1<<i)) in selected for i in range(4))
                    for v in range(16) if v not in selected]
        moments = [sum(comb(k,j) for k in exterior) for j in (3,4)]
        signature = [len(selected),inner,*(spectrum[d] for d in range(1,5)),*moments]
        if windows:
            lengths = []
            unseen = set(selected)
            while unseen:
                queue = [unseen.pop()]
                for vertex in queue:
                    for axis in range(4):
                        neighbour = vertex^(1<<axis)
                        if neighbour in unseen:
                            unseen.remove(neighbour)
                            queue.append(neighbour)
                lengths.append(len(queue))
            signature.extend(sum(max(0,n-lag) for n in lengths) for lag in range(2,8))
        result.add(tuple(signature))
    return sorted(result)


class Matrix:
    def __init__(self):
        self.i = []
        self.j = []
        self.coeff = []
        self.rhs = []

    def add(self, terms, rhs):
        for j,coefficient in terms:
            if coefficient:
                self.i.append(len(self.rhs))
                self.j.append(j)
                self.coeff.append(coefficient)
        self.rhs.append(rhs)

    def sparse(self, width):
        return coo_matrix((self.coeff,(self.i,self.j)),shape=(len(self.rhs),width)).tocsr()


def endpoint_rectangles(distance):
    other = 9-distance
    forest = forest_masks()

    @lru_cache(maxsize=None)
    def capacity(mask):
        return max((shape&mask).bit_count() for shape in forest)

    for lo_x in range(distance+1):
        for hi_x in range(lo_x,distance+1):
            for lo_y in range(other+1):
                for hi_y in range(lo_y,other+1):
                    values = []
                    for a in range(max(0,4-other),min(distance,4)+1):
                        mask_x = (1<<a)-1
                        cap = 0
                        for x in range(distance-a+1):
                            for y in range(other-4+a+1):
                                window = sum(
                                    1<<v for v in range(16)
                                    if lo_x<=x+(v&mask_x).bit_count()<=hi_x
                                    and lo_y<=y+(v>>a).bit_count()<=hi_y
                                )
                                cap += (comb(distance-a,x)*comb(other-4+a,y)*capacity(window))
                        values.append(cap)
                    yield (lo_x,hi_x,lo_y,hi_y),min(values)


def constrain_two_endpoints(length,distance,valid,boundary,allocate,equal,upper):
    # Reversal and translation preserve the lag histogram and exchange
    # the two endpoint margins, so their common mean is admissible.
    states = {}
    for step in range(length+1):
        if step==0:
            positions = [(0,0)]
        elif step==length:
            positions = [(distance,0)]
        else:
            positions = [(x,y) for x in range(distance+1) for y in range(10-distance)
                         if x+y in valid[step] and distance-x+y in valid[length-step]]
        states[step] = {point:allocate() for point in positions}
        equal.add(((i,1) for i in states[step].values()),1)
        if not 0<step<length:
            continue
        for lag,from_origin in ((step,True),(length-step,False)):
            for hamming in valid[lag]:
                terms = [(index,1) for (x,y),index in states[step].items()
                         if (x+y if from_origin else distance-x+y)==hamming]
                equal.add(terms+[(boundary[lag,hamming],-1)],0)

    for step in range(length):
        here,there = states[step],states[step+1]
        edges = {(p,q):allocate() for p in here for q in there
                 if abs(p[0]-q[0])+abs(p[1]-q[1])==1}
        for p,var in here.items():
            equal.add([(i,1) for (u,v),i in edges.items() if u==p]+[(var,-1)],0)
        for q,var in there.items():
            equal.add([(i,1) for (u,v),i in edges.items() if v==q]+[(var,-1)],0)

    by_position = [(x,y,i) for layer in states.values() for (x,y),i in layer.items()]
    for (lo_x,hi_x,lo_y,hi_y),capacity in endpoint_rectangles(distance):
        if capacity < length+1:
            upper.add(((i,1) for x,y,i in by_position if lo_x<=x<=hi_x and lo_y<=y<=hi_y),capacity)


def solve(length, endpoint, control=None, q5=(), windows=False, paired_endpoints=False):
    nodes = length+1
    valid = {
        lag: (range(1,2) if lag==1 else range(2+lag%2,min(lag,9)+1,2))
        for lag in range(1,nodes)
    }
    fits = [(lag,d) for lag,row in valid.items() for d in row]
    bounds = []

    def allocate(value=None):
        index = len(bounds)
        bounds.append((0,None) if value is None else (value,value))
        return index

    actual = None if control is None else Counter(
        (j-i,(u^control[j]).bit_count())
        for i,u in enumerate(control) for j in range(i+1,nodes)
    )
    pair = {p:allocate(None if actual is None else actual[p]) for p in fits}
    boundary = {p:allocate() for p in fits}
    equal, upper = Matrix(),Matrix()

    for lag,distances in valid.items():
        equal.add(((pair[lag,d],1) for d in distances),nodes-lag)
        equal.add(((boundary[lag,d],1) for d in distances),1)
    equal.add([(pair[length,endpoint],1)],1)
    equal.add([(boundary[length,endpoint],1)],1)

    # Right extension loses the unique pair already touching the last vertex.
    # Boundary distances also move by one bit as their first vertex changes.
    def flow(lag, values, losses=None):
        adjacency = {
            (a,b):allocate()
            for a in valid[lag] for b in valid[lag+1] if abs(a-b)==1
        }
        for a in valid[lag]:
            terms = [(index,1) for (u,v),index in adjacency.items() if u==a]
            terms.append((values[lag,a],-1))
            if losses is not None:
                terms.append((losses[lag,a],1))
            equal.add(terms,0)
        for b in valid[lag+1]:
            terms = [(index,1) for (u,v),index in adjacency.items() if v==b]
            equal.add(terms+[(values[lag+1,b],-1)],0)

    for lag in range(1,length):
        flow(lag,pair,boundary)
        flow(lag,boundary)
    for d in range(1,10):
        upper.add(((boundary[lag,a],1) for lag,a in fits if a==d),comb(9,d))

    if paired_endpoints:
        constrain_two_endpoints(length,endpoint,valid,boundary,allocate,equal,upper)

    outside = [allocate() for _ in range(10)]
    equal.add(((i,1) for i in outside),512-nodes)
    equal.add(((i,k) for k,i in enumerate(outside)),9*nodes-2*length)
    terms = [(i,comb(k,2)) for k,i in enumerate(outside)]
    terms += [(pair[lag,d],-2) for lag,d in fits if d==2]
    equal.add(terms,2-nodes)

    q4 = local_signatures(windows)
    support = {}
    if windows:
        cap = [0,1,2,4,7,max(row[2] for row in q5 if row[0] == row[2]+1)]
        window_states = {}
        boundary_support = {}
        for lag in range(1,14):
            row = [(d,s) for d in valid[lag] for s in range(d,min(9,(lag+d)//2)+1)
                   if s>=len(cap) or lag<=cap[s]]
            window_states[lag] = row
            for d,s in row:
                support[lag,d,s] = allocate()
                boundary_support[lag,d,s] = allocate()
            for d in valid[lag]:
                distances = [s for x,s in row if x==d]
                for counts,unrefined in ((support,pair),(boundary_support,boundary)):
                    terms = [(counts[lag,d,s],1) for s in distances]
                    equal.add(terms+[(unrefined[lag,d],-1)],0)
        for lag in range(1,13):
            here,there = window_states[lag],window_states[lag+1]
            valid_edges = [
                ((d,s),(e,t)) for d,s in here for e,t in there
                if (s==t and abs(d-e)==1) or (t==s+1 and e==d+1)
            ]
            for counts,removed in ((support,boundary_support),(boundary_support,None)):
                walks = {edge:allocate() for edge in valid_edges}
                for d,s in here:
                    terms = [(x,1) for (a,b),x in walks.items() if a==(d,s)]
                    if removed is not None:
                        terms.append((removed[lag,d,s],1))
                    equal.add(terms+[(counts[lag,d,s],-1)],0)
                for e,t in there:
                    terms = [(x,1) for (a,b),x in walks.items() if b==(e,t)]
                    equal.add(terms+[(counts[lag+1,e,t],-1)],0)

    sections = [(4,q4)]
    if q5:
        sections.append((5,q5))
    for dimension,signatures in sections:
        face = [allocate() for _ in signatures]
        equal.add(((i,1) for i in face),comb(9,dimension)*(1<<(9-dimension)))
        equal.add(((i,s[0]) for i,s in zip(face,signatures)),comb(9,dimension)*nodes)
        equal.add(((i,s[1]) for i,s in zip(face,signatures)),comb(7,dimension-2)*(nodes-2))
        for d in range(1,dimension+1):
            weight = comb(9-d,dimension-d)
            terms = [(pair[lag,a],-weight) for lag,a in fits if a==d]
            terms += [(i,s[d+1]) for i,s in zip(face,signatures)]
            equal.add(terms,0)
        for j in range(3,dimension+1):
            terms = [(i,s[dimension+j-1]) for i,s in zip(face,signatures)]
            terms.extend((i,-comb(9-j,dimension-j)*comb(k,j)) for k,i in enumerate(outside))
            equal.add(terms,0)
        if windows:
            max_window = 7 if dimension==4 else 13
            for lag in range(2,max_window+1):
                index = 2*dimension+lag-2
                terms = [(i,s[index]) for i,s in zip(face,signatures)]
                terms.extend((i,-comb(9-s,dimension-s)) for (l,d,s),i in support.items()
                             if l==lag and s<=dimension)
                equal.add(terms,0)

    spectra = [[krawtchouk(d,r)/comb(9,r) for d in range(10)] for r in range(1,10)]
    for k in range(65):
        phase = [cos(2*pi*k*lag/128) for lag in range(nodes)]
        for row in spectra:
            upper.add(((pair[lag,d],-2*phase[lag]*row[d]) for lag,d in fits),nodes)

    sz = len(bounds)
    objective = np.zeros(sz)
    result = linprog(objective,A_eq=equal.sparse(sz),b_eq=equal.rhs,
                     A_ub=upper.sparse(sz),b_ub=upper.rhs,bounds=bounds,method="highs")
    report = dict(length=length,endpoint_distance=endpoint,control=control is not None,
                  variables=sz,inequalities=len(upper.rhs),equalities=len(equal.rhs),
                  q4_signatures=len(q4),q5_signatures=len(q5),windows=windows,paired_endpoints=paired_endpoints,solver_status=result.status,message=result.message)
    if result.success:
        report["status"] = "FEASIBLE_RELAXATION"
        report["distance_counts"] = [round(sum(result.x[pair[lag,d]] for lag,a in fits if a==d),6)
                                     for d in range(1,10)]
        report["max_equality_error"] = float(np.max(np.abs(result.eqlin.residual)))
    else:
        report["status"] = "NUMERICAL_INFEASIBLE" if result.status==2 else "UNKNOWN"
    return report


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--control",type=Path)
    parser.add_argument("--q5-signatures",type=Path)
    parser.add_argument('--windows',action='store_true')
    parser.add_argument('--paired-endpoints',action='store_true')
    args = parser.parse_args()
    q5 = []
    if args.q5_signatures:
        q5 = [tuple(map(int,line.split())) for line in args.q5_signatures.read_text().splitlines()]
        assert q5 and len(set(q5))==len(q5) and all(len(row)==(22 if args.windows else 10) for row in q5)
    assert not args.windows or q5
    if args.control:
        with gzip.open(args.control,"rt") as path:
            points = list(map(int,next(path).split()))
        checked = solve(len(points)-1,(points[0]^points[-1]).bit_count(),points,q5,args.windows,args.paired_endpoints)
        print(json.dumps(checked),flush=True)
        assert checked["status"]=="FEASIBLE_RELAXATION"
    for endpoint in (3,5,7,9):
        print(json.dumps(solve(221,endpoint,q5=q5,windows=args.windows,paired_endpoints=args.paired_endpoints)),flush=True)
