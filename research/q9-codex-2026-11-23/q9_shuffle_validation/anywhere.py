"""All disjoint physical 3/4-step permutation windows, chosen by the solver."""
from pathlib import Path
import sys,json
from itertools import permutations,combinations
from collections import defaultdict,Counter
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from common import D,R,vertices,word,induced
def unrestricted(w,budget,allowed=(3,4),defect_cap=0):
    pool=IDPool();cnf=[];p=vertices(w);n=len(w);cover=[[] for _ in w];cause=defaultdict(list);options=[];domain=[{v} for v in p]
    for k in allowed:
        for i in range(n-k+1):
            orig=w[i:i+k]
            for seq in set(permutations(orig)):
                if list(seq)==orig:continue
                path=[v^p[i] for v in vertices(seq)]
                if not induced(path,9):continue
                # Identity at both boundaries follows from equal axis multiplicities.
                assert path[-1]==p[i+k]
                oid=pool.id(('block',i,seq));options.append((oid,i,seq))
                for j in range(i,i+k):cover[j].append(oid)
                for t,x in enumerate(path[1:-1],i+1):
                    domain[t].add(x);cause[t,x].append(oid);cnf.append([-oid,pool.id((t,x))])
    def amo(ls):
        if len(ls)>1:cnf.extend(CardEnc.atmost(ls,1,vpool=pool,encoding=EncType.ladder).clauses)
    for ls in cover:amo(ls)
    state=defaultdict(list)
    for t,vs in enumerate(domain):
        ls=[]
        for v in sorted(vs):
            x=pool.id((t,v));state[v].append((t,x));ls.append(x)
            if v!=p[t]:cnf.append([-x,*cause[t,v]])
        cnf.append(ls);amo(ls)
    violations={}
    for v,ls in state.items():
        amo([x for t,x in ls])
        for b in range(9):
            u=v^1<<b
            if u<=v:continue
            for t,x in ls:
                for j,y in state.get(u,[]):
                    if abs(t-j)>1:
                        cl=[-x,-y]
                        if defect_cap:
                            ij=tuple(sorted((t,j)))
                            if ij not in violations:violations[ij]=pool.id(('bad',ij))
                            cl.append(violations[ij])
                        cnf.append(cl)
    if defect_cap and len(violations)>defect_cap:cnf.extend(CardEnc.atmost(list(violations.values()),defect_cap,vpool=pool,encoding=EncType.seqcounter).clauses)
    with Cadical195(bootstrap_with=cnf) as s:
        s.set_phases([-oid for oid,_,_ in options]);s.conf_budget(budget);ans=s.solve_limited();con=s.accum_stats()['conflicts']
        if ans is not True:return ['UNSAT' if ans is False else 'UNKNOWN',con,None,[]]
        pos=set(s.get_model());used=[];q=list(w)
        for z,i,seq in options:
            if z in pos:q[i:i+len(seq)]=seq;used.append([i,list(seq)])
        path=vertices(q);assert len(set(path))==len(path) and sum((v^u).bit_count()==1 for j,v in enumerate(path) for u in path[:max(0,j-1)])<=defect_cap
        return ['FOUND',con,path,used]
def corpus(n):
    files=[R/'q9_via_q10'/f'cross_seeds_{n}.txt',R/'q9_via_q10/monotone_near.words']
    bank={}
    for f in files:
        for i,l in enumerate(f.read_text().splitlines()):
            if f.suffix=='.txt':
                tok=l.split();v=list(map(int,tok[2:]));assert len(v)==n+1 and all((x^y).bit_count()==1 for x,y in zip(v,v[1:]));w=word(v);error=int(tok[1])
            else:
                if len(l)!=n:continue
                w=list(map(int,l));v=vertices(w);error=sum((v[j]^v[k]).bit_count()<=1 for j in range(n+1) for k in range(j-1))
            bank.setdefault(tuple(w),(error,f.name,i))
    return sorted((err,nm,ix,list(w)) for w,(err,nm,ix) in bank.items())
if __name__=='__main__':
    n,count,budget=map(int,sys.argv[1:]);name=f'any{n}';ct=Counter()
    if n==191:
        base=[json.loads(l) for l in (D/'control191_3129.jsonl').read_text().splitlines()]
        bank=[(a['errors'],'scrambled',a['t'],list(map(int,a['w']))) for a in base]
    else:bank=corpus(n)
    with (D/(name+'.jsonl')).open('w') as fout:
        for err,src,i,w in bank[:count]:
            st,c,p,used=unrestricted(w,budget);ct[st]+=1;row=dict(src=src,i=i,reported_defects=err,w=''.join(map(str,w)),status=st,c=c)
            if p:row.update(path=p,used=used)
            print(json.dumps(row,separators=(',',':')),file=fout,flush=True)
            if n!=191 and p:break
    print(json.dumps(dict(count=ct,available=len(bank))))
