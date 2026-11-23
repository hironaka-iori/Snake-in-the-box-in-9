"""Separate adjacency CNF and DRAT search for CP-SAT-infeasible branches."""
from itertools import combinations
from pathlib import Path
import json,sys,os
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
B=Path(__file__).resolve().parent;R=B.parent

def cnf(r, goal_vertices=193, with_vars=False):
    w=(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()[r['archive']]
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    ep=p[-1] if r['side'] else p[0];y=r['new_vertex']
    nbs=lambda v:{v^1<<i for i in range(9)}
    blockers=nbs(y)&set(p)-{ep}
    released={v for v in p if any((v^u).bit_count()<=r['radius'] for u in blockers)}-{ep}
    yes=set(p)-released|{y};no=set(blockers)
    for v in yes:
        fixed=nbs(v)&yes
        if len(fixed)==2:no.update(nbs(v)-yes)
    assert not no&yes
    possible=sorted(set(range(512))-no);nv=IDPool();x={v:nv.id(('chosen',v)) for v in possible}
    F=CNF();[F.append([x[v]]) for v in yes]
    ends={v:nv.id(('end',v)) for v in possible if v.bit_count()%2==r['majority']}
    def exact(ls,k):
        if k>len(ls) or k<0:F.append([]);return
        if k==0:F.extend([[-v] for v in ls]);return
        F.extend(CardEnc.equals(ls,k,vpool=nv,encoding=EncType.totalizer).clauses)
    exact(list(ends.values()),2)
    for colour in (0,1):
        cand=[v for v in possible if v.bit_count()%2==colour]
        exact([x[v] for v in cand if v not in yes],goal_vertices//2+int(colour==r['majority'])-sum(v in yes for v in cand))
    for v in possible:
        if v in ends:F.append([-ends[v],x[v]])
        nb=nbs(v);req=2-len(nb&yes);lits=[x[u] for u in sorted(nb-yes) if u in x]
        if v in ends:lits.append(ends[v])
        if not 0<=req<=len(lits):F.append([-x[v]]);continue
        for t in combinations(lits,req+1):F.append([-x[v],*[-a for a in t]])
        for t in combinations(lits,len(lits)-req+1):F.append([-x[v],*t])
    for v in possible:
        for i,j in combinations(range(9),2):
            q={v,v^1<<i,v^1<<j,v^1<<i^1<<j}
            if v==min(q) and q<=x.keys():F.append([-x[t] for t in q-yes])
    return (F,x,ends) if with_vars else F

if __name__=='__main__':
    cases={}
    for f in sys.argv[1:]:
        for l in (B/f).read_text().splitlines():
            r=json.loads(l)
            if r['status']=='INFEASIBLE':cases[r['rank']]=r
    if os.getenv('Q9_ALL'):
        data=[json.loads(l) for l in (R/'q9_uncovered_endpoint_relocation.jsonl').read_text().splitlines()]
        old=[r|dict(majority=b['majority']) for r in data for b in r['branches'] if b['status']=='UNKNOWN']
        cases={rank:old[idx]|dict(conflicts=0) for rank,(_,__,idx) in enumerate(json.loads((B/'rank.json').read_text())) if rank%int(os.getenv('Q9_STEPS','1'))==int(os.getenv('Q9_SHARD','0')) and not (B/('rank'+str(rank)+'.drat')).exists()}
    for rank,r in sorted(cases.items(),key=lambda z:z[1]['conflicts']):
        F=cnf(r);tag='rank'+str(rank)
        with Solver(name='cadical195',bootstrap_with=F,with_proof=True) as s:
            s.conf_budget(int(os.getenv('Q9_BUDGET','85000')));ans=s.solve_limited()
            if ans is False:
                F.to_file(str(B/(tag+'.cnf')))
                (B/(tag+'.drat')).write_text('\n'.join(s.get_proof())+'\n')
            print(json.dumps(dict(rank=rank,result='CNF_UNSAT' if ans is False else 'UNKNOWN' if ans is None else 'SAT_RELAXATION',conflicts=s.accum_stats()['conflicts'])),flush=True)
