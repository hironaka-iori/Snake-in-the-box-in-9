"""Necessary integer conditions on a three-coordinate projection of a 221-edge snake."""
import argparse
from itertools import combinations, permutations, product
import json
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from verify_q9_free_dimension_cuts import edge7


def edge6(c):
    if c == 0:
        return 0
    if c <= 2:
        return 26
    if c == 3:
        return 25
    return min(24,32-c)


def formula(counts, end, exact_cuts=(), star_cuts=()):
    f=CNF()
    pool=IDPool()
    def unary(n):
        row=[pool.id() for _ in range(n)]
        f.extend([[-b,a] for a,b in zip(row,row[1:])])
        return row
    def card(xs, n, encode=CardEnc.equals):
        f.extend(encode(xs,n,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    def bind(inputs, output):
        card(inputs+[-x for x in output],len(output))
    def exact(row,value):
        return ([row[value-1]] if value else []) + ([-row[value]] if value<len(row) else [])
    def forest(edges, components, cap):
        for c in range(len(components)+1):
            if cap(c) < len(edges):
                f.append([*(-x for x in exact(components,c)),-edges[cap(c)]])
    def flatten(rows):
        return [x for row in rows for x in row]

    edges=[unary(26) for _ in range(8)]
    components=[unary(1+sum(counts)//2) for _ in range(8)]
    crossing={}
    for i,k in enumerate(counts):
        axis=[]
        for a in range(8):
            b=a^(1<<i)
            if a>b:
                continue
            row=unary(k)
            crossing[a,b]=row
            axis.append(row)
            # A contacting 26-edge face can meet only a face with at most 23 edges.
            f.extend([[-row[0],-edges[a][25],-edges[b][23]],
                      [-row[0],-edges[b][25],-edges[a][23]]])
            f.extend([[-row[0],-edges[a][24],-edges[b][24],components[face][1]]
                      for face in (a,b)])
            f.append([-row[0],-edges[a][24],-edges[b][24],
                      components[a][2],components[b][2]])
            if k>=2:
                f.extend([[-row[1],-edges[a][25],-edges[b][22]],
                          [-row[1],-edges[b][25],-edges[a][22]]])
                for face in (a,b):
                    f.append([-row[1],-edges[a][24],-edges[b][24],components[face][2]])
            if k>=3:
                f.extend([[-row[2],-edges[a][25],-edges[b][21]],
                          [-row[2],-edges[b][25],-edges[a][21]]])
                f.extend([[-row[2],-edges[a][24],-edges[b][23]],
                          [-row[2],-edges[b][24],-edges[a][23]]])
            if k>=4:
                f.extend([[-row[3],-edges[a][24],-edges[b][22]],
                          [-row[3],-edges[b][24],-edges[a][22]]])
            for A,B,r in exact_cuts:
                if r>k:
                    continue
                for (ea,ca),(eb,cb) in ((A,B),(B,A)):
                    if ca>len(components[a]) or cb>len(components[b]):
                        continue
                    match=exact(edges[a],ea)+exact(components[a],ca)
                    match+=exact(edges[b],eb)+exact(components[b],cb)+exact(row,r)
                    f.append([-x for x in match])
        card(flatten(axis),k)
    for v in range(8):
        neighbors=[v^(1<<axis) for axis in range(3)]
        for e,c,leaves in star_cuts:
            if c>len(components[v]):
                continue
            center=exact(edges[v],e)+exact(components[v],c)
            for order in permutations(neighbors,len(leaves)):
                match=list(center)
                for w,(ew,cw,rw) in zip(order,leaves):
                    r=crossing[tuple(sorted((v,w)))]
                    if rw>len(r) or (cw is not None and cw>len(components[w])):
                        break
                    if cw is None:
                        match += [edges[w][ew-1],r[rw-1]]
                    else:
                        match+=exact(edges[w],ew)+exact(components[w],cw)+exact(r,rw)
                else:
                    f.append([-x for x in match])
    for subset in range(2,256,2):
        boundary = [r[0] for (a,b),r in crossing.items() if bool(subset>>a&1) != bool(subset>>b&1)]
        for v in range(1,8):
            if subset>>v&1:
                f.append([-components[v][0],*boundary])
    for v,(e,c) in enumerate(zip(edges,components)):
        forest(e,c,edge6)
        card(e+c,32,CardEnc.atmost)
        incident=flatten(x for ends,x in crossing.items() if v in ends)
        duplicate=[pool.id() for _ in c]
        f.extend([a,-b] for a,b in zip(c,duplicate))
        f.extend([-a,b] for a,b in zip(c,duplicate))
        card(incident+[-x for x in c+duplicate],
             2*len(c)-int(v==0)-int(v==end))
    card(flatten(edges),221-sum(counts))
    for i,k in enumerate(counts):
        combined = {}
        # Refine each Q7 face by recombining two neighbouring Q6 faces.
        for (a,b), r in crossing.items():
            if a^b!=1<<i:
                continue
            merged_e=unary(52)
            merged_c=unary(1+(sum(counts)-k+2)//2)
            combined[a]=(merged_e,merged_c)
            bind(edges[a]+edges[b]+r,merged_e)
            card(components[a]+components[b]+[-x for x in r+merged_c],
                 len(r)+len(merged_c))
            forest(merged_e,merged_c,edge7)
            pair_total=sum(counts)-k
            if 17<=pair_total<=21:
                card(merged_e+merged_c,56,CardEnc.atmost)
                card(merged_e+merged_c,55 if pair_total==17 else 54,CardEnc.atleast)
            if pair_total==17:
                f.extend([[merged_e[50]],[-merged_e[51]]])
        for (a,b),r in crossing.items():
            if a^b==1<<i:
                continue
            ea,ca=combined[a & ~(1<<i)]
            eb,cb=combined[b & ~(1<<i)]
            f.extend([[-r[0],-ea[51],-eb[50]],[-r[0],-eb[51],-ea[50]]])
            sibling=tuple(sorted((a^(1<<i),b^(1<<i))))
            if a>sibling[0]:
                continue
            other=crossing[sibling]
            for r1 in range(5):
                r2=4-r1
                if r1>len(r) or r2>len(other):
                    continue
                guards=([-r[r1-1]] if r1 else []) + ([-other[r2-1]] if r2 else [])
                f.extend([[*guards,-ea[51],-eb[49],-cb[3]],
                          [*guards,-eb[51],-ea[49],-ca[3]]])
    return f,edges,components,crossing


def run(counts,end,budget,out,checker,exact_cuts=(),star_cuts=()):
    f,es,cs,xs=formula(counts,end,exact_cuts,star_cuts)
    with Cadical195(bootstrap_with=f,with_proof=True) as sat:
        sat.conf_budget(budget)
        result=sat.solve_limited()
        if result is None:
            return dict(status="UNKNOWN",**sat.accum_stats())
        if result:
            m=set(sat.get_model())
            occupancy=lambda rows:[sum(x in m for x in row) for row in rows]
            return dict(status="FEASIBLE_RELAXATION",edges=occupancy(es),components=occupancy(cs),
                        crossings=occupancy(xs.values()),**sat.accum_stats())
        stem=out/("q9_triple_"+"_".join(map(str,counts))+"_end"+str(end))
        f.to_file(str(stem)+".cnf")
        Path(str(stem)+".drat").write_text("\n".join(sat.get_proof())+"\n")
        r=subprocess.run([checker,str(stem)+".cnf",str(stem)+".drat"],capture_output=True,check=True)
        assert b"s VERIFIED" in r.stdout
        return dict(status="UNSAT_DRAT_verified",proof=str(stem)+".drat",**sat.accum_stats())


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("out",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--maximum",type=int,default=29)
    parser.add_argument("--exact-cuts",type=Path)
    parser.add_argument("--star-cuts",type=Path)
    a=parser.parse_args()
    stars=json.loads(a.star_cuts.read_text()) if a.star_cuts else []
    cuts=json.loads(a.exact_cuts.read_text()) if a.exact_cuts else []
    for counts in product(range(3,a.maximum-5),repeat=3):
        if not counts[0]<=counts[1]<=counts[2] or sum(counts)>a.maximum:
            continue
        if min(sum(p) for p in combinations(counts,2))<17:
            continue
        end=sum((k%2)<<i for i,k in enumerate(counts))
        print(json.dumps(dict(counts=counts,end=end,status="STARTED")),flush=True)
        print(json.dumps(dict(counts=counts,end=end,**run(counts,end,200000,a.out,a.checker,cuts,stars))),flush=True)
