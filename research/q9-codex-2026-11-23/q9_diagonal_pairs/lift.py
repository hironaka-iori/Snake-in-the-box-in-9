"""Find induced paths while freely switching sheets of a diagonal translation quotient."""
from itertools import combinations
from pathlib import Path
from collections import Counter
import json,random,sys
from pysat.solvers import Minicard
D=Path(__file__).resolve().parent;R=D.parent
NB=[tuple(v^(1<<d) for d in range(9)) for v in range(512)]
def path(w):
    p=[0]
    for d in w:p.append(p[-1]^1<<int(d))
    return p
def valid(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((v^u).bit_count()==1)==(i==j+1) for i,v in enumerate(p) for j,u in enumerate(p[:i]))
def solve(p,m,target,release,budget):
    N=target+1; assert 0<m<512 and m.bit_count()>=3
    rep=lambda u:min(u,u^m)
    count=Counter(map(rep,p)); cols=set(count);cross={v:tuple(rep(u) for u in NB[v] if rep(u) in cols) for v in cols}
    assert all(len(ns)==len(set(ns)) for ns in cross.values())
    pool={y for v in cols for y in (v,v^m)};possible={v for v,ns in cross.items() if len(ns)<=4}
    old={v for v,n in count.items() if n==2};assert old<=possible
    with Minicard() as sat:
        def at(ls,k):
            if k<0:sat.add_clause([])
            elif k<len(ls):sat.add_atmost(ls,k)
        def exact(ls,k):at(ls,k);at([-v for v in ls],len(ls)-k)
        Z=lambda v:1025+v
        for v in sorted(cols):
            x,y=v+1,(v^m)+1;sat.add_clause([x,y])
            if v not in possible:sat.add_clause([-x,-y])
            else:
                z=Z(v);sat.add_clause([-x,-y,z]);sat.add_clause([-z,x]);sat.add_clause([-z,y])
        # Either global translate represents the same quotient selection.
        gauge=min(cols-possible) if cols-possible else None
        if gauge is not None:sat.add_clause([gauge+1])
        exact([Z(v) for v in sorted(possible)],N-len(cols))
        at([-Z(v) for v in sorted(old)],release)
        for v,adj in cross.items():
            zs=[Z(u) for u in adj if u in possible]
            at(zs,2)
            if v in possible:
                for group in combinations(zs,5-len(adj)):sat.add_clause([-Z(v),*[-z for z in group]])
        ends=[]
        for v in sorted(pool):
            x=v+1;e=513+v;ends.append(e);ns=[u+1 for u in NB[v] if u in pool]
            sat.add_clause([-e,x]);sat.add_clause([-x,*ns])
            for a,b,c in combinations(ns,3):sat.add_clause([-x,-a,-b,-c])
            for a,b in combinations(ns,2):sat.add_clause([-e,-a,-b])
            for j in range(len(ns)):sat.add_clause([-x,e,*ns[:j],*ns[j+1:]])
            if target%2==0:sat.add_clause([-e,1600 if v.bit_count()%2 else -1600])
        exact(ends,2)
        hint=set(p)
        if gauge is not None and gauge not in hint:hint={x^m for x in hint}
        sat.set_phases([v+1 if v in hint else -v-1 for v in sorted(pool)])
        cuts=0
        while True:
            left=budget-sat.accum_stats()['conflicts']
            if left<=0:return 'UNKNOWN',cuts,None
            sat.conf_budget(left);ok=sat.solve_limited()
            if ok is not True:return ('UNSAT' if ok is False else 'UNKNOWN'),cuts,None
            model=set(sat.get_model());chosen={v for v in pool if v+1 in model}
            ends=[v for v in chosen if len(set(NB[v])&chosen)==1];assert len(ends)==2
            seq=[ends[0]];rest=chosen-{ends[0]}
            while (nxt:=set(NB[seq[-1]])&rest):
                assert len(nxt)==1;v=next(iter(nxt));seq.append(v);rest.remove(v)
            if not rest:
                assert len(seq)==N and valid(seq) and set(map(rep,seq))==cols
                return 'FOUND',cuts,seq
            while rest:
                comp=[rest.pop()]
                for v in comp:
                    add=rest.intersection(NB[v]);comp.extend(add);rest-=add
                sat.add_clause([-v-1 for v in comp]);cuts+=1
def main():
    kind,target,rel,cap,limit,offset=sys.argv[1:];target,rel,cap,limit,offset=map(int,(target,rel,cap,limit,offset))
    file=R/('q9_disagreement_mix/two_banks189.words' if kind=='fresh' else 'q9_far189_spring_20261121/comparison191.words')
    words=file.read_text().split()
    jobs=[(j,m) for j in range(len(words)) for m in range(512) if m.bit_count()>=3]
    random.Random(571602).shuffle(jobs)
    for j,m in jobs[offset:offset+limit]:
        s,c,w=solve(path(words[j]),m,target,rel,cap)
        print(json.dumps(dict(row=j,mask=m,status=s,cuts=c,vertices=w),separators=(',',':')),flush=True)
        if w and target>=192:return
if __name__=='__main__':main()
