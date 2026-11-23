"""Audit a fixed minority using opposite-vertex variables and a SAT solver."""
from itertools import combinations
from collections import Counter
import gzip,sys,json
from pathlib import Path
from pysat.solvers import Cadical195
D=Path(__file__).resolve().parent
NEIGH=[{v^(1<<d) for d in range(9)} for v in range(512)]
def solve(side):
    fixed=set(side); opposite={x for v in fixed for x in NEIGH[v] if 1<=len(NEIGH[x]&fixed)<=2}
    tips=[v for v in opposite if len(NEIGH[v]&fixed)==1]
    def exactly_two(s,vs):
        n=len(vs)
        if n<2:s.add_clause([]);return
        for a,b,c in combinations(vs,3):s.add_clause([-a-1,-b-1,-c-1])
        for x in vs:s.add_clause([y+1 for y in vs if y!=x])
    cuts=0
    with Cadical195() as sat:
        exactly_two(sat,tips)
        for v in side:exactly_two(sat,list(NEIGH[v]&opposite))
        while sat.solve():
            m=set(sat.get_model()); chosen=fixed|{x for x in opposite if x+1 in m}
            termini=[x for x in chosen if len(NEIGH[x]&chosen)==1]
            assert len(termini)==2
            rest=chosen.copy();p=[termini[0]];rest.remove(p[0])
            while (nexts:=NEIGH[p[-1]]&rest):
                assert len(nexts)==1
                u=next(iter(nexts));p.append(u);rest.remove(u)
            if not rest:
                assert len(p)==2*len(side)+1 and len(set(p))==len(p)
                assert all(((x^y).bit_count()==1)==(i==j+1) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
                return p,cuts
            while rest:
                cycle=[rest.pop()]
                for x in cycle:
                    new=NEIGH[x]&rest;cycle.extend(new);rest-=new
                sat.add_clause([-v-1 for v in cycle if v not in fixed]);cuts+=1
    return None,cuts
def main():
    lines=(D/'parity_control.log').read_text().splitlines()
    for s in lines:
        if s.startswith('FOUND'):
            p=list(map(int,s.split()[1:]));assert len(p)==191
            assert solve(p[1::2])[0] is not None
    summary=Counter(); batches=Counter()
    with gzip.open(D/'minority_candidates.gz','rt') as f:
        for l in f:
            if l.startswith('ROW'):
                _,r,pairs,one,two,eligible,unknown,hit=l.split()
                assert int(eligible)==batches['sets'] and not int(unknown) and not int(hit)
                batches.clear();summary['rows']+=1;continue
            side=list(map(int,l.split()[1:]));assert len(side)==96
            path,cuts=solve(side);summary['sets']+=1;batches['sets']+=1;summary['cycle_cuts']+=cuts
            if path:
                print(json.dumps({'vertices':path}));return
    assert summary['rows']==304 and summary['sets']==10654
    print(json.dumps(dict(summary,known_190_controls=10)))
if __name__=='__main__':main()
