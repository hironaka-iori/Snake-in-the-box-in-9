from itertools import combinations
from pathlib import Path
from collections import Counter
import os,json,sys,time
from banks import D,path,check
from pysat.formula import IDPool,CNF
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
W=(D/'donors.words').read_text().split(); R=json.loads((D/'references.json').read_text())
def search(i,c,target,limit,known=None):
    low=path(W[i]); roots={low[0],low[-1]}; allowed=sorted(set(range(256))-set(low[1:-1])); ids=IDPool(); F=CNF(); x={v:ids.id(('occ',v)) for v in allowed}; ep={v:ids.id(('end',v)) for v in allowed if c==-1 or (1+v.bit_count())%2==c}
    def eq(ls,n):F.extend(CardEnc.equals(ls,n,vpool=ids,encoding=EncType.totalizer).clauses)
    for v in roots:F.append([x[v]])
    for k in range(2):eq([x[v] for v in allowed if v.bit_count()%2==k],(target+1)//2+int(1-k==c)-sum(v.bit_count()%2==1-k for v in low))
    eq(list(ep.values()),2)
    if c==-1:
        assert target%2==1
        eq([ep[v] for v in ep if v.bit_count()%2==0],1)
    for v in allowed:
        z=[x[v^1<<b] for b in range(8) if v^1<<b in x];n=2-int(v in roots)
        if v in ep:z.append(ep[v]);F.append([-ep[v],x[v]])
        if n>len(z):F.append([-x[v]]);continue
        for a in combinations(z,n+1):F.append([-x[v],*[-t for t in a]])
        for a in combinations(z,len(z)-n+1):F.append([-x[v],*a])
        for b,d in combinations(range(8),2):
            q=(v,v^1<<b,v^1<<d,v^1<<b^1<<d)
            if v==min(q) and all(u in x for u in q):F.append([-x[u] for u in q])
    pins=[]
    if known:
        arm1,arm2=known
        pins=[] if os.getenv('Q9_NO_PINS') else arm1[1::3]+arm2[1::3];F.extend([[x[v]] for v in pins]);hint=[x[v] if v in arm1 or v in arm2 else -x[v] for v in allowed]
    cuts=[];start=time.monotonic();witness=None;iterations=0;tag=f'sat_{target}_{i}_{c}'+('_hint' if os.getenv('Q9_NO_PINS') else '')
    with Solver(name='cadical195',bootstrap_with=F,with_proof=False) as s:
        if known:s.set_phases(hint)
        while True:
            left=limit-s.accum_stats()['conflicts'];iterations+=1
            if left<=0:ans=None;break
            s.conf_budget(left);ans=s.solve_limited()
            if ans is not True:break
            md=set(s.get_model());occ={v+256 for v in allowed if x[v] in md}|set(low);adj={v:[v^1<<b for b in range(9) if v^1<<b in occ] for v in occ};ends=[v for v in occ if len(adj[v])==1];assert len(ends)==2 and min(ends)>=256
            seen=set();chain=[ends[0]];v=ends[0];prev=-1
            while True:
                seen.add(v);n=[t for t in adj[v] if t!=prev];
                if not n:break
                prev,v=v,n[0];chain.append(v)
            if len(chain)==len(occ):check(chain);assert len(chain)==target+1;witness=chain;break
            while occ-seen:
                todo=[next(iter(occ-seen))];cyc=set(todo)
                while todo:
                    v=todo.pop()
                    for u in adj[v]:
                        if u not in cyc:cyc.add(u);todo.append(u)
                assert all(len(adj[v])==2 for v in cyc);seen.update(cyc);cut=[-x[v-256] for v in sorted(cyc) if v>=256 and v-256 not in roots];cuts.append(cut);s.add_clause(cut)
        count=s.accum_stats()['conflicts']
    if ans is False and (not known or os.getenv('Q9_EXPORT_PROOF')):
        F.extend(cuts)
        with Solver(name='cadical195',bootstrap_with=F,with_proof=True) as certified:
            if known:certified.set_phases(hint)
            assert not certified.solve();F.to_file(str(D/(tag+'.cnf')));(D/(tag+'.drat')).write_text('\n'.join(certified.get_proof())+'\n')
        (D/(tag+'.cuts.json')).write_text(json.dumps(cuts))
    if witness:(D/(tag+'.paths')).write_text(' '.join(map(str,[target,i,*witness]))+'\n')
    print(json.dumps(dict(id=i,c=c,target=target,pins=len(pins),limit=limit,conflicts=count,answer=ans,cycles=len(cuts),seconds=round(time.monotonic()-start,3))),flush=True)
if __name__=='__main__':
    ids=[int(x) for x in sys.argv[1].split(',')]; mode=sys.argv[2];budget=int(sys.argv[3]);
    for i in ids:
        if mode=='control':
            n,_,_,_,a,b=R[str(i)];u=path(a);v=path(b,path(W[i])[-1]);check([256+t for t in u[::-1]]+path(W[i])+[256+t for t in v]);assert n%2==0;search(i,(1+u[-1].bit_count())%2,n,budget,(u,v))
        elif mode=='hint':
            n,_,_,_,a,b=R[str(i)];u=path(a);v=path(b,path(W[i])[-1]);assert __import__('os').getenv('Q9_NO_PINS');
            for c in (0,1):search(i,c,192,budget,(u,v))
        else:
            for c in (0,1):search(i,c,192,budget)
