"""Exact Q8 completion with explicit port, endpoint, and color counts for 192."""
import argparse,json,random
from pathlib import Path
from itertools import combinations
from pysat.solvers import Minicard
from verify_q9_center_avoidance import verify
N=[{x^(1<<i) for i in range(8)} for x in range(256)]

def solve(A,target,budget,hint):
    deg={v:len(N[v]&A) for v in A}
    iso={v for v,d in deg.items() if d==0}
    tip={v for v,d in deg.items() if d==1}
    P=set(range(256))-{v for v,d in deg.items() if d==2}
    if len(iso)>2 or any(d>2 for d in deg.values()):return 'UNSAT',None
    total=target+1
    with Minicard() as s:
        def card(lits,k):
            if k<0 or k>len(lits):s.add_clause([]);return
            s.add_atmost(lits,k);s.add_atmost([-v for v in lits],len(lits)-k)
        for v in iso:s.add_clause([v+1])
        card([v+1 for v in P],total-len(A))
        for color in (0,1):
            cnt=sum(u.bit_count()%2==color for u in A)
            slots=[v+1 for v in P if (v.bit_count()+1)%2==color]
            lim=(total+1)//2-cnt
            if lim<0:s.add_clause([])
            else:s.add_atmost(slots,lim)
        elits=[-v-1 for v in tip]
        for v in P:
            x=v+1;e=v+257;nb=[w+1 for w in N[v]&P];elits.append(e)
            s.add_clause([-e,x])
            if v in A:
                for a,b in combinations(nb,2):s.add_clause([-x,-a,-b])
                for a in nb:s.add_clause([-e,-a])
                s.add_clause([-x,e,*nb])
            else:
                s.add_clause([-x,*nb])
                for a,b,c in combinations(nb,3):s.add_clause([-x,-a,-b,-c])
                for a,b in combinations(nb,2):s.add_clause([-e,-a,-b])
                for j in range(len(nb)):s.add_clause([-x,e,*nb[:j],*nb[j+1:]])
            for a,b in combinations([w for w in N[v]&P if w>v],2):
                w=v^a^b
                if w>v and w in P:s.add_clause([-x,-a-1,-b-1,-w-1])
        card(elits,2-len(iso))
        if target%2==0:
            # The two global endpoints must have the same parity in Q9.
            t=513
            for v in iso:s.add_clause([t if v.bit_count()%2 else -t])
            for v in tip:s.add_clause([v+1,t if v.bit_count()%2 else -t])
            for v in P:s.add_clause([-(v+257),t if not v.bit_count()%2 else -t])
        s.set_phases([v+1 if v in hint else -v-1 for v in P])
        while True:
            rem=budget-s.accum_stats()['conflicts']
            if rem<=0:return 'UNKNOWN',None
            s.conf_budget(rem);ok=s.solve_limited()
            if ok is not True:return ('UNKNOWN' if ok is None else 'UNSAT'),None
            m=set(s.get_model());B={v for v in P if v+1 in m};full=A|{256+v for v in B}
            adj=lambda x:{x^(1<<d) for d in range(9)}&full
            ends=[x for x in full if len(adj(x))==1];assert len(ends)==2 and all(1<=len(adj(x))<=2 for x in full)
            w=[ends[0]];rest=full-set(w)
            while new:=adj(w[-1])&rest:
                assert len(new)==1;y=new.pop();rest.remove(y);w.append(y)
            if not rest:
                verify(w);assert len(w)==total
                return 'FOUND',w
            while rest:
                comp=[rest.pop()]
                for x in comp:
                    nb=adj(x)&rest;comp.extend(nb);rest-=nb
                s.add_clause([-(v-256)-1 for v in comp if v>=256])
if __name__=='__main__':
    import sys
    bank=Path(sys.argv[1]).read_text().splitlines();num=int(sys.argv[2]);budget=int(sys.argv[3])
    p=list(map(int,Path('q9_forest_ports_control.log').read_text().splitlines()[0].split()[1:]))
    ctrl=solve({v for v in p if v<256},191,30000,{v-256 for v in p if v>=256})
    assert ctrl[0]=='FOUND';print(json.dumps(['control',*ctrl]),flush=True)
    order=list(range(len(bank)));random.Random(984411).shuffle(order)
    for i in order[:num]:
        a=set(map(int,bank[i].split()[1:]));st,w=solve(a,192,budget,set())
        print(json.dumps([i,len(a),st,w],separators=(',',':')),flush=True)
        if w:break
