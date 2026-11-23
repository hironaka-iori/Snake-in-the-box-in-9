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
def word(seq):
    w=[(u^v).bit_length()-1 for u,v in zip(seq,seq[1:])]
    def standard(ds):
        names={}
        return ''.join(str(names.setdefault(d,len(names))) for d in ds)
    return min(standard(w),standard(w[::-1]))
def solve(p,m,target,release,budget,extra=(),free=(),removed=None,excluded=None):
    variable=target<0;target=abs(target);N=target+1; assert 0<m<512 and m.bit_count()>=3
    rep=lambda u:min(u,u^m)
    count=Counter(map(rep,p)); original=set(count);need=original-set(free);cols=original|set(extra);opt=cols-need;cross={v:tuple(rep(u) for u in NB[v] if rep(u) in cols) for v in cols}
    assert all(len(ns)==len(set(ns)) for ns in cross.values())
    pool={y for v in cols for y in (v,v^m)};possible={v for v,ns in cross.items() if len(need.intersection(ns))<=4}
    old={v for v,n in count.items() if n==2};assert old<=possible
    with Minicard() as sat:
        def at(ls,k):
            if k<0:sat.add_clause([])
            elif k<len(ls):sat.add_atmost(ls,k)
        def exact(ls,k):at(ls,k);at([-v for v in ls],len(ls)-k)
        Z=lambda v:1025+v
        O=lambda v:1700+v
        for v in sorted(cols):
            x,y=v+1,(v^m)+1
            if v in need:sat.add_clause([x,y])
            else:
                o=O(v);sat.add_clause([-o,x,y]);sat.add_clause([-x,o]);sat.add_clause([-y,o])
            if v not in possible:sat.add_clause([-x,-y])
            else:
                z=Z(v);sat.add_clause([-x,-y,z]);sat.add_clause([-z,x]);sat.add_clause([-z,y])
        # Either global translate represents the same quotient selection.
        gauge=min(need-possible) if need-possible else None
        if gauge is not None:sat.add_clause([gauge+1])
        size=[Z(v) for v in sorted(possible)]+[O(v) for v in sorted(opt)]
        if variable:at([-a for a in size],len(size)-N+len(need))
        else:exact(size,N-len(need))
        at([-Z(v) for v in sorted(old)],release)
        for v,adj in cross.items():
            zs=[Z(u) for u in adj if u in possible]
            if v in need:at(zs,2)
            else:
                for a,b,c in combinations(zs,3):sat.add_clause([-O(v),-a,-b,-c])
            if v in possible:
                for group in combinations(zs,5-len(need.intersection(adj))):sat.add_clause([-Z(v),*[-z for z in group]])
        ends=[]
        for v in sorted(pool):
            x=v+1;e=513+v;ends.append(e);ns=[u+1 for u in NB[v] if u in pool]
            sat.add_clause([-e,x]);sat.add_clause([-x,*ns])
            for a,b,c in combinations(ns,3):sat.add_clause([-x,-a,-b,-c])
            for a,b in combinations(ns,2):sat.add_clause([-e,-a,-b])
            for j in range(len(ns)):sat.add_clause([-x,e,*ns[:j],*ns[j+1:]])
            if not variable and target%2==0:sat.add_clause([-e,1600 if v.bit_count()%2 else -1600])
        exact(ends,2)
        hint=set(p)
        if gauge is not None and gauge not in hint:hint={x^m for x in hint}
        if removed is not None:at([-v-1 for v in hint],removed)
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
                assert (len(seq)>=N if variable else len(seq)==N) and valid(seq) and need<=set(map(rep,seq))<=cols
                if excluded and word(seq) in excluded:
                    sat.add_clause([-v-1 for v in seq])
                    continue
                return 'FOUND',cuts,seq
            while rest:
                comp=[rest.pop()]
                for v in comp:
                    add=rest.intersection(NB[v]);comp.extend(add);rest-=add
                sat.add_clause([-v-1 for v in comp]);cuts+=1
def main():
    kind,target,cap,trials,width=sys.argv[1:6];removed=int(sys.argv[6]) if len(sys.argv)>6 else None;target,cap,trials,width=map(int,(target,cap,trials,width))
    rng=random.Random(548931+width+target); masks=[m for m in range(512) if m.bit_count()>=3]
    words=(R/('q9_disagreement_mix/two_banks189.words' if kind=='fresh' else 'q9_far189_spring_20261121/comparison191.words')).read_text().split()
    rng.shuffle(masks)
    for i in range(trials):
        j=0 if width==0 else rng.randrange(len(words));p=path(words[j]);m=masks[i%len(masks)]
        if rng.randrange(2):p=p[::-1]
        rep=lambda u:min(u,u^m)
        if kind=='control':
            p=p[:-2];c=set(map(rep,p))
            if not all(rep(v) in c for v in (set(path(words[j]))-set(p))):continue
        c=set(map(rep,p));neigh=lambda u:{rep(v) for v in NB[u]}
        tip=p[-1];near=neigh(tip)|{rep(tip)}
        area=set(near)
        for v in near:area.update(neigh(v))
        def sample(s,k):return rng.sample(sorted(s),min(k,len(s)))
        extra=sample(near-c,width);extra+=sample(area-c-set(extra),width)
        free=sample(area&c,width)
        status,cuts,w=solve(p,m,target,256,cap,extra,free,removed)
        print(json.dumps(dict(row=j,mask=m,seed_edges=len(p)-1,extra=extra,free=free,status=status,cuts=cuts,vertices=w),separators=(',',':')),flush=True)
        if w and abs(target)>=192:return
if __name__=='__main__':main()
