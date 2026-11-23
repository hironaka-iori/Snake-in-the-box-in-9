from pathlib import Path
import json,sys,random
from itertools import combinations
from pysat.solvers import Minicard,Cadical195
from pysat.card import CardEnc,EncType
D=Path(__file__).resolve().parent;NB=[{x^(1<<k) for k in range(8)} for x in range(256)]
def solve(L,target,budget,hint=(),cross=-1,solver='mini'):
    L=set(L);lf={v:NB[v]&L for v in L};A={v for v in range(256) if v not in L or len(lf[v])<2};T=A&L
    assert all(len(s)<=2 for s in lf.values());free=sorted(A)
    def comps(s,nb):
        rem=set(s);out=[]
        while rem:
            q=[rem.pop()]
            for v in q:
                more=nb[v]&rem;q.extend(more);rem-=more
            out.append(q)
        return out
    lowparts=comps(L,NB);clauses=[];cards=[];ends=[]
    def atmost(z,k):
        if k<0:clauses.append([])
        elif k<len(z):cards.append((list(z),k))
    def atleast(z,k):atmost([-x for x in z],len(z)-k)
    def eq(z,k):atmost(z,k);atleast(z,k)
    for part in lowparts:
        ports=[v+1 for v in T.intersection(part)]
        clauses.append(ports)
    for v in T:
        if len(lf[v])==1:ends.append(-v-1)
        else:clauses.append([v+1])
    isolated=sum(len(lf[v])==0 for v in L)
    if cross>=0:eq([v+1 for v in T],cross)
    needed=target+1-len(L);atleast([v+1 for v in A],needed)
    for parity in (0,1):
        bottom=sum(x.bit_count()%2==parity for x in L)
        qt=[v+1 for v in A if (v.bit_count()+1)%2==parity]
        atleast(qt,(target+1)//2-bottom)
    for v in A:
        e=257+v;ends.append(e);clauses.append([-e,v+1])
        z=[w+1 for w in sorted(NB[v]&A)]+[e];need=2-int(v in L)
        if len(z)<need:clauses.append([-v-1]);continue
        for c in combinations(z,need+1):clauses.append([-v-1,*[-x for x in c]])
        for c in combinations(z,len(z)-need+1):clauses.append([-v-1,*c])
    eq(ends,2-isolated)
    # Every two-coordinate square of the upper cube contains at most three selected vertices.
    for i,j in combinations(range(8),2):
        mask=1<<i|1<<j
        for v in A:
            if v&mask:continue
            sq=(v,v^(1<<i),v^(1<<j),v^mask)
            if all(w in A for w in sq):clauses.append([-w-1 for w in sq])
    if solver=='mini':
        s=Minicard(bootstrap_with=clauses)
        for z,k in cards:s.add_atmost(z,k)
    else:
        top=512
        for z,k in cards:
            c=CardEnc.atmost(z,k,top_id=top,encoding=EncType.seqcounter);top=max(top,c.nv);clauses.extend(c.clauses)
        s=Cadical195(bootstrap_with=clauses)
    # Hints influence polarity only. An empty upper hint gives a genuinely fresh upper-layer search.
    hints=set(hint);s.set_phases([v+1 if v in hints else -v-1 for v in A]+[257+v if v in hints and len((NB[v]&hints))+int(v in L)==1 else -257-v for v in A])
    status='LIMIT';calls=0;w=None
    adj={x:({y for y in lf[x]}|({x+256} if x in A else set())) for x in L}
    adj.update({x+256:({y+256 for y in NB[x]&A}|({x} if x in L else set())) for x in A})
    try:
        while calls<150:
            calls+=1;remain=budget-s.accum_stats()['conflicts']
            if remain<=0:break
            s.conf_budget(remain);res=s.solve_limited()
            if res is False:status='UNSAT';break
            if res is None:break
            model=set(s.get_model());upper={v for v in A if v+1 in model};sel=L|{v+256 for v in upper}
            assert len(sel)>target
            groups=comps(sel,adj)
            if len(groups)==1:
                q=[next(v for v in sel if len(adj[v]&sel)==1)];rem=sel-{q[0]}
                while rem:
                    nv,=adj[q[-1]]&rem;rem.remove(nv);q.append(nv)
                status='FOUND';w=q;break
            root=min(L)
            for group in groups:
                if root in group:continue
                border=set().union(*(adj[v] for v in group))-set(group);guard=[] if set(group)&L else [-(group[0]-256)-1]
                s.add_clause(guard+[v-255 for v in border if v>=256])
        return status,calls,s.accum_stats()['conflicts'],w
    finally:s.delete()
def main():
    mode=sys.argv[1]
    if mode=='control':
        for r in json.loads((D/'controls.json').read_text()):
            for warm in (True,False):
                goal=191 if warm else 120
                z=solve(r['lower'],goal,12000,r['upper_hint'] if warm else (),2)
                print(r['ref'],warm,goal,z[0],z[2],*(z[3] or []),flush=True)
        return
    data=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
    budget=int(sys.argv[2]);stride=int(sys.argv[3]);ss=sys.argv[4]
    for ix,r in enumerate(data):
        if ix%stride:continue
        for cross in [-1] if len(sys.argv)<6 else list(map(int,sys.argv[5].split(','))):
            z=solve(r['lower'],192,budget,(),cross,ss)
            print(r['id'],cross,z[0],z[1],z[2],*(z[3] or []),flush=True)
            if z[3]:return
    print('DONE',flush=True)
if __name__=='__main__':main()

