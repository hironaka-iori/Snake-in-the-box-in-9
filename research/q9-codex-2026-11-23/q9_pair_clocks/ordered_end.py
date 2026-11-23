"""The two steps of every consecutive 2-edge block may trade places independently."""
from collections import defaultdict,Counter
from search import axes,validate,D
from pysat.solvers import Cadical195
import json,random,sys
def solve(w,ps,s,cap):
    ng=len(ps);grp={a:i for i,row in enumerate(ps) for a in row};grp[s]=ng
    clauses=[];num=ng;start=tuple(range(1,ng+1));clauses.extend([[-v] for v in start]);evens=[(0,start)];middles=[];warm=[];twins={}
    def var():
        nonlocal num
        num+=1;return num
    phys=0
    for t in range(0,len(w)-1,2):
        a,b=w[t:t+2];g,h=grp[a],grp[b];mask,prev=evens[-1];end=list(prev);choices=[]
        if g==h:
            if g==ng:return 'UNSAT',None,0
            half=list(prev);half[g]=var();warm.append(half[g] if (phys^(1<<a))&(1<<ps[g][0]) else -half[g])
            end[g]=-prev[g];choices.append((mask^1<<g,tuple(half),None))
        else:
            for k in (g,h):
                if k<ng:
                    end[k]=var();warm.append(end[k] if (phys^(1<<a)^(1<<b))&(1<<ps[k][0]) else -end[k])
            order=var();warm.append(order)
            for k,guard in [(g,order),(h,-order)]:
                mid=list(prev)
                if k<ng:mid[k]=end[k]
                choices.append((mask^1<<k,tuple(mid),guard))
        phys^=(1<<a)^(1<<b);evens.append((mask^1<<g^1<<h,tuple(end)));middles.append(choices)
    if len(w)%2:
        g=grp[w[-1]];mask,prev=evens[-1];mid=list(prev)
        if g<ng:mid[g]=var();warm.append(mid[g] if (phys^(1<<w[-1]))&(1<<ps[g][0]) else -mid[g])
        middles.append([(mask^(1<<g),tuple(mid),None)])
    table=defaultdict(list);constraints=set()
    def protect(x,y,omit,guard):
        cl=[]
        for k,(u,v) in enumerate(zip(x,y)):
            if k==omit or u==v:continue
            if u==-v:return True
            pair=tuple(sorted((u,v)));alt=tuple(sorted((-u,-v)));key=min(pair,alt)
            if key not in twins:
                z=var();twins[key]=z
                clauses.extend(([-z,u,v],[-z,-u,-v]))
            cl.append(twins[key])
        if guard is not None:cl.append(-guard)
        if not cl:return False
        constraints.add(tuple(sorted(cl)));return True
    for j,(m,state) in enumerate(evens):
        for i in table[m]:
            if not protect(state,evens[i][1],-1,None):return 'UNSAT',None,0
        table[m].append(j)
    for t,choices in enumerate(middles):
        for m,state,guard in choices:
            for k in range(ng+1):
                for j in table[m^1<<k]:
                    if j!=t and j!=t+1 and not protect(state,evens[j][1],k,guard):return 'UNSAT',None,0
    clauses.extend(constraints)
    with Cadical195(bootstrap_with=clauses) as sol:
        sol.set_phases(warm);sol.conf_budget(cap);r=sol.solve_limited();c=sol.accum_stats()['conflicts']
        if r!=True:return ('UNSAT' if r is False else 'UNKNOWN'),None,c
        model=set(sol.get_model())
        def chosen(lit):return (abs(lit) in model)==(lit>0)
        def decode(m,row):
            x=((m>>ng)&1)<<s
            for k,(a,b) in enumerate(ps):
                bit=int(chosen(row[k]));x|=bit<<a;x|=(bit^((m>>k)&1))<<b
            return x
        p=[decode(*evens[0])]
        for t,opts in enumerate(middles):
            m,state,_=next(o for o in opts if o[2] is None or chosen(o[2]))
            p.append(decode(m,state))
            if t+1<len(evens):p.append(decode(*evens[t+1]))
        assert validate(p) and len(p)==len(w)+1
        return 'FOUND',p,c
def tree(dims,rng):
    perm=list(range(9));rng.shuffle(perm);links=[]
    for j in range(1,9):links.append([perm[j],perm[rng.randrange(j)]])
    rng.shuffle(links);return links
def q8input(n,rng,arch,ranked):
    if n==192 and rng.randrange(2):
        row=rng.choice(ranked);w=row[-1];masks=row[-2];links=[[d for d in range(9) if m>>d&1] for m in masks]
    else:
        w=rng.choice(arch);i=rng.randrange(len(w)-(n+1)//2+1);w=w[i:i+(n+1)//2];links=tree(9,rng)
    return [z for c in w for z in links[int(c)]][:n]
def main(n,trials,cap,seed):
    rng=random.Random(seed);arch=[w for w in (D.parent/'q8_catalogue_96_98.words').read_text().split() if len(w)>=(n+1)//2]
    ranked=json.loads((D.parent/'q9_tree_mobile/ranked_sources.json').read_text())
    near=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    stats=Counter()
    for i in range(trials):
        src='q8' if i%2==0 else 'near'
        w=q8input(n,rng,arch,ranked) if src=='q8' else rng.choice(near)
        ds=list(range(9));rng.shuffle(ds);ps=[tuple(ds[j:j+2]) for j in range(0,8,2)];s=ds[-1]
        st,p,c=solve(w,ps,s,cap);stats[src+'_'+st]+=1
        if p:
            print(json.dumps(dict(found=p,seed=w,ps=ps,s=s,source=src)),flush=True);break
        if i%30==29:print(json.dumps(dict(tested=i+1,counts=stats)),flush=True)
    print(json.dumps(dict(done=True,counts=stats)),flush=True)
if __name__=='__main__':main(*map(int,sys.argv[1:]))
