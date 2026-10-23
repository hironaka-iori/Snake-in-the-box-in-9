"""Two-centre adaptation of the independent exact-quotient model.

No SAT encoder, unary counter, or reported upstream witness value is reused.
INFEASIBLE remains an unchecked solver result, not a Lean refutation.
"""
import argparse,collections,hashlib,itertools,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.sat.python import cp_model

def window(dirs):
    w=[0]
    for a in dirs:w.append(w[-1]^(1<<a))
    return w

def model(n,dirs,bounds,radius=4,M=12,cap=None,fixed=None):
    win=window(dirs);centres=win[1:-1]
    B={v for v in range(1<<n) if min((v^c).bit_count() for c in centres)<=radius}
    md=cp_model.CpModel(); x={v:md.new_bool_var(f'x{v}') for v in sorted(B)}
    for v in win:md.add(x[v]==1)
    if fixed is not None:
        for v in B:md.add(x[v]==int(v in fixed))
    endpoints=[]
    for v in sorted(B):
        ns=[x[v^(1<<a)] for a in range(n) if (v^(1<<a)) in B]
        md.add(sum(ns)<=2).only_enforce_if(x[v])
        if len(ns)==n:
            e=md.new_bool_var(f'end{v}');endpoints.append(e)
            md.add(e<=x[v])
            md.add(sum(ns)==2-e).only_enforce_if(x[v])
    md.add(sum(endpoints)<=2)
    empties={}
    def empty(sq):
        k=tuple(sorted(sq))
        if k not in empties:
            z=md.new_bool_var('empty'+','.join(map(str,k)));empties[k]=z
            md.add(sum(x[v] for v in k)==0).only_enforce_if(z)
            md.add(sum(x[v] for v in k)>=1).only_enforce_if(z.Not())
        return empties[k]
    for c,(lo,hi) in zip(centres,bounds):
        single=[]
        for a,b in itertools.combinations(range(n),2):
            k=[c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)]
            assert set(k)<=B
            z=md.new_bool_var(f'alpha{c}_{a}_{b}')
            md.add(sum(x[v] for v in k)==0).only_enforce_if(z)
            md.add(sum(x[v] for v in k)>=1).only_enforce_if(z.Not())
            single.append(z)
        md.add(sum(single)>=lo);md.add(sum(single)<=hi)
    # Share terms for path neighbors vanish; all other neighbors are unselected.
    multiplicity=collections.Counter()
    for i,c in enumerate(centres,1):
        if i not in (1,6):continue
        for a in range(n):
            q=c^(1<<a)
            if q not in (win[i-1],win[i+1]):multiplicity[q]+=1
    quotient={}
    for q in sorted(multiplicity):
        ns=[q^(1<<a) for a in range(n)];assert set(ns)<=B
        d=md.new_int_var(1,n,f'd{q}');md.add(d==sum(x[v] for v in ns))
        es=[]
        for a,b in itertools.combinations(range(n),2):
            sq=[q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)]
            assert set(sq)<=B
            es.append(empty(sq))
        e=md.new_int_var(0,n*(n-1)//2,f'e{q}');md.add(e==sum(es))
        u=md.new_int_var(0,M*n*(n-1)//2,f'u{q}');quotient[q]=u
        # All pairs are included: no additional unproved geometric cutoff.
        md.add_allowed_assignments([e,d,u],[(ee,dd,M*ee//dd) for dd in range(1,n+1) for ee in range(n*(n-1)//2+1)])
    total=sum(mult*quotient[q] for q,mult in multiplicity.items())
    if cap is not None:md.add(total<=cap)
    # Cheap sound cycle cuts, followed by all-length cycle separation during search.
    cuts=set()
    for v in sorted(B):
        for a,b in itertools.combinations(range(n),2):
            sq=frozenset((v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))
            if sq<=B and sq not in cuts:
                md.add(sum(x[w] for w in sq)<=3);cuts.add(sq)
    for v in sorted(B):
        for axes in itertools.combinations(range(n),3):
            if any(v&(1<<a) for a in axes):continue
            cube=[v^sum((1<<axes[a]) for a in range(3) if mask&(1<<a)) for mask in range(8)]
            for opposite in range(4):
                cyc=frozenset(cube[j] for j in range(8) if j not in (opposite,7-opposite))
                if cyc<=B and cyc not in cuts:
                    md.add(sum(x[w] for w in cyc)<=5);cuts.add(cyc)
    return md,x,total,win,B,cuts

def census(S,n,centres,M=12):
    pairs=list(itertools.combinations(range(n),2))
    deg={q:sum((q^(1<<a)) in S for a in range(n)) for q in range(1<<n)}
    e={q:sum(not any(w in S for w in (q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b))) for a,b in pairs) for q in range(1<<n)}
    alpha=[sum(not any(w in S for w in (c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b))) for a,b in pairs) for c in centres]
    share=[sum(M*e[q]//deg[q] for a in range(n) if deg[q:=c^(1<<a)]) for c in centres]
    unseen=set(S);cycles=[]
    while unseen:
        stack=[next(iter(unseen))];comp=[]
        while stack:
            v=stack.pop()
            if v not in unseen:continue
            unseen.remove(v);comp.append(v)
            stack.extend(v^(1<<a) for a in range(n) if (v^(1<<a)) in unseen)
        if all(deg[v]==2 for v in comp):cycles.append(sorted(comp))
    return dict(alpha=alpha,share=share,total_share=sum(share),cycles=cycles,degree=deg)
