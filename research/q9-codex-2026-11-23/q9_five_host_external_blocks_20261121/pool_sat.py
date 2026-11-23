from pathlib import Path
import sys,json
from itertools import combinations
from pysat.solvers import Minicard
D=Path(__file__).resolve().parent;NB=[{v^(1<<d) for d in range(9)} for v in range(512)]
def solve(domain,goal,budget=4000):
    domain=set(domain);n=goal+1
    if len(domain)<n:return 'UNSAT',0,None
    # A path with n vertices fits in one connected component. For these hosts two such components cannot coexist.
    def parts(s):
        r=set(s);gs=[]
        while r:
            q=[r.pop()]
            for v in q:
                for w in nb[v]&r:r.remove(w);q.append(w)
            gs.append(q)
        return gs
    nb={v:NB[v]&domain for v in domain}
    big=[g for g in parts(domain) if len(g)>=n]
    if not big:return 'UNSAT',0,None
    assert len(big)==1;domain=set(big[0]);nb={v:NB[v]&domain for v in domain}
    with Minicard() as sol:
        def atmost(a,b):
            if b<0:sol.add_clause([])
            elif b<len(a):sol.add_atmost(a,b)
        vs=[v+1 for v in domain];atmost([-z for z in vs],len(vs)-n)
        for c in (0,1):
            cls=[v+1 for v in domain if v.bit_count()%2==c]
            atmost([-z for z in cls],len(cls)-n//2)
        ends=[]
        for v in domain:
            e=v+513;ends.append(e);sol.add_clause([-e,v+1])
            z=[w+1 for w in nb[v]]+[e]
            # A selected v has degree 2-e.
            for group in combinations(z,3):sol.add_clause([-v-1]+[-w for w in group])
            if len(z)<2:sol.add_clause([-v-1])
            else:
                for group in combinations(z,len(z)-1):sol.add_clause([-v-1,*group])
        atmost(ends,2);atmost([-e for e in ends],len(ends)-2)
        sol.set_phases(vs)
        for nr in range(100):
            left=budget-sol.accum_stats()['conflicts']
            if left<=0:return 'LIMIT',nr,None
            sol.conf_budget(left);ok=sol.solve_limited()
            if ok is False:return 'UNSAT',nr+1,None
            if ok is None:return 'LIMIT',nr+1,None
            model=set(sol.get_model());selected={v for v in domain if v+1 in model}
            assert len(selected)>=n
            gs=sorted(parts(selected),key=len,reverse=True)
            if len(gs)==1:
                q=[next(v for v in selected if len(nb[v]&selected)==1)];r=selected-set(q)
                while r:
                    nxt,=nb[q[-1]]&r;r.remove(nxt);q.append(nxt)
                return 'FOUND',nr+1,q
            # A connected solution containing one selected vertex inside and one outside this component must cross its border.
            outside=gs[0][0]
            for g in gs[1:]:
                gsset=set(g);boundary=set().union(*(nb[v] for v in g))-gsset
                sol.add_clause([-g[0]-1,-outside-1,*[v+1 for v in boundary]])
        return 'LIMIT',100,None
def rows(f):
    return [list(map(int,l.split())) for l in Path(f).read_text().splitlines()]
if __name__=='__main__':
    if sys.argv[1]=='control':
        for i in range(5):
            dom=rows(D/f'control{i}.in')[0];st,r,w=solve(dom,191);assert st=='FOUND';print(i,st,*w)
        raise SystemExit
    hosts=rows(sys.argv[1]);mode=sys.argv[3]
    for ln,l in enumerate(Path(sys.argv[2]).open()):
        if not l.startswith(tuple(mode.split('+'))):continue
        tag,row,n,other,*xs=l.split();row=int(row);ext=list(map(int,xs))
        st,r,w=solve(hosts[row]+ext,192)
        print(st,row,'extras',*ext,'rounds',r,*(w or []),flush=True)
        if w:break
    print('DONE',flush=True)

