from pathlib import Path
from collections import defaultdict
from itertools import combinations
import json,sys,random
from pysat.solvers import Minicard,Cadical195
D=Path(__file__).resolve().parent
NE=[[v^1<<k for k in range(9)] for v in range(512)]
closed=[{v,*NE[v]} for v in range(512)]
def solve(w,g,rad,budget,engine='mini'):
    groups=list(map(int,g));steps=[[],[],[]];cnt=[0,0,0];base=[tuple(cnt)]
    for ch in w:
        a=int(ch);k=groups[a];steps[k].append(a);cnt[k]+=1;base.append(tuple(cnt))
    end=tuple(cnt);n=len(w)
    tracks=[]
    for seq in steps:
        p=[0]
        for d in seq:p.append(p[-1]^1<<d)
        tracks.append(p)
    # Each clock triple determines one physical point. Each global step advances precisely one clock.
    vs=[];L=[];curr=512
    for t,q in enumerate(base):
        row={}
        for a in range(max(0,q[0]-rad),min(q[0]+rad,end[0])+1):
            for b in range(max(0,q[1]-rad),min(q[1]+rad,end[1])+1):
                c=t-a-b
                if not 0<=c<=end[2] or abs(c-q[2])>rad:continue
                pos=(a,b,c);curr+=1;row[pos]=(curr,tracks[0][a]^tracks[1][b]^tracks[2][c])
        L.append(row)
    def nxt(s):
        a,b,c=s;return [(a+1,b,c),(a,b+1,c),(a,b,c+1)]
    def prev(s):
        a,b,c=s;return [(a-1,b,c),(a,b-1,c),(a,b,c-1)]
    while True:
        before=sum(map(len,L))
        for t in range(1,n+1):L[t]={a:v for a,v in L[t].items() if any(q in L[t-1] for q in prev(a))}
        if not L[-1]:return 'EMPTY',0,0,0,None
        for t in reversed(range(n)):L[t]={a:v for a,v in L[t].items() if any(q in L[t+1] for q in nxt(a))}
        forced=defaultdict(list)
        for t,row in enumerate(L):
            xs={v for _,v in row.values()}
            if not xs:return 'EMPTY',0,0,0,None
            if len(xs)>10:continue
            common=set.intersection(*(closed[x] for x in xs))
            for v in common:forced[v].append(t)
        for t in range(n+1):
            L[t]={a:(u,v) for a,(u,v) in L[t].items() if not forced[v] or forced[v][0]>=t-1 and forced[v][-1]<=t+1}
        after=sum(map(len,L))
        if after==before:break
    pool=defaultdict(list);clauses=[];known=[]
    for t,row in enumerate(L):
        for q,(u,v) in row.items():
            pool[v].append(u);clauses.append([-u,v+1])
            if t:clauses.append([-u,*[L[t-1][s][0] for s in prev(q) if s in L[t-1]]])
            if t<n:clauses.append([-u,*[L[t+1][s][0] for s in nxt(q) if s in L[t+1]]])
            if q==base[t]:known.append(u)
    for v,items in pool.items():
        clauses.append([-v-1,*items]);nb=[x+1 for x in NE[v] if x in pool]
        ends=(v==0 or v==(tracks[0][-1]^tracks[1][-1]^tracks[2][-1]))
        for ss in combinations(nb,2 if ends else 3):clauses.append([-v-1,*[-x for x in ss]])
    cls=Minicard if engine=='mini' else Cadical195
    with cls(bootstrap_with=clauses) as sat:
        extra=curr
        def amo(items):
            nonlocal extra
            if len(items)<2:return
            if engine=='mini':sat.add_atmost(items,1);return
            if len(items)<6:
                for a,b in combinations(items,2):sat.add_clause([-a,-b])
                return
            prev=0
            for j,x in enumerate(items):
                if prev:sat.add_clause([-prev,-x])
                if j+1<len(items):
                    extra+=1;sat.add_clause([-x,extra])
                    if prev:sat.add_clause([-prev,extra])
                    prev=extra
        for row in L:
            z=[u for u,v in row.values()];sat.add_clause(z);amo(z)
        for items in pool.values():amo(items)
        sat.set_phases(known)
        assumptions=[]
        if engine=='cd':
            raw=[tracks[0][q[0]]^tracks[1][q[1]]^tracks[2][q[2]] for q in base]
            bad={u for i,x in enumerate(raw) for j,y in enumerate(raw[:i-1] if i>=2 else []) if (x^y).bit_count()<=1 for u in (i,j)}
            assumptions=[L[t][q][0] for t,q in enumerate(base) if q in L[t] and all(abs(t-b)>5 for b in bad)]
        for it in range(65):
            remain=budget-sat.accum_stats()['conflicts']
            if remain<=0:return 'LIMIT',after,budget,len(clauses),None
            sat.conf_budget(remain);ok=sat.solve_limited(assumptions=assumptions);conf=sat.accum_stats()['conflicts']
            if ok:break
            if ok is None:return 'LIMIT',after,conf,len(clauses),None
            core=set(sat.get_core() or [])
            if not core:return 'UNSAT',after,conf,len(clauses),None
            assumptions=[v for v in assumptions if v not in core] if it<10 else []
        else:raise AssertionError('unreleased assumptions')
        model={v for v in sat.get_model() if v>0};p=[next(v for u,v in row.values() if u in model) for row in L]
        assert len(p)==len(set(p))==n+1 and all(((x^y).bit_count()==1)==(j==k+1) for j,x in enumerate(p) for k,y in enumerate(p[:j]))
        word=''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]));return 'FOUND',after,conf,len(clauses),word
def main():
    src,rad,cap,take,seed=sys.argv[1:];rad,cap,take,seed=map(int,(rad,cap,take,seed));rng=random.Random(seed)
    rs=(D/src).read_text().splitlines();head=min(take//2,len(rs));tail=rng.sample(range(head,len(rs)),min(len(rs)-head,take-head));ids=[*range(head),*tail]
    for i in ids:
        w,g,*_=rs[i].split();st,states,c,cl,z=solve(w,g,rad,cap)
        print(json.dumps(dict(i=i,status=st,states=states,conflicts=c,clauses=cl,word=z),separators=(',',':')),flush=True)
        if z and len(z)>=192:return
if __name__=='__main__':main()
