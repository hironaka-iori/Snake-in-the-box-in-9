import argparse,gzip,itertools,json
from pathlib import Path
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Cadical195
D=Path(__file__).resolve().parent
bank=[list(map(int,l.split())) for l in gzip.open(D.parent/'q9_port_followup_public191.txt.gz','rt')]
def check(p,axes,budget,minimum=193):
    vpool=IDPool(start_from=1200);cl=[]
    def lower(v,k):
        if k>len(v):cl.append([])
        elif k>0:cl.extend(CardEnc.atleast(v,k,vpool=vpool,encoding=EncType.totalizer).clauses)
    def occ(v):return v+1
    for a in axes:
        F={x&~(1<<a) for x in p}; points=[v for v in range(512) if not v&(1<<a)];extra=[]
        for v in points:
            b=v^(1<<a);l,r=occ(v),occ(b)
            if v in F:cl.append([l,r])
            else:
                t=vpool.id();extra.append(t);cl.append([-t,l,r])
            if sum((v^(1<<d)) in F for d in range(9) if d!=a)>2:cl.append([-l,-r])
            else:
                t=vpool.id();extra.append(t);cl.extend([[-t,l],[-t,r]])
        lower(extra,minimum-len(F))
    A,B=axes;req=[{x&~(1<<a) for x in p} for a in axes];ce=[];mins=0
    for x in range(512):
        if x&((1<<A)|(1<<B)):continue
        cell=(x,x^(1<<A),x^(1<<B),x^(1<<A)^(1<<B));bounds=[sum((v&~(1<<a)) in req[j] for v in cell)//2 for j,a in enumerate(axes)]
        mn=max(bounds);mins+=mn
        for k in range(mn+1,4):
            t=vpool.id();ce.append(t)
            for comb in itertools.combinations(cell,5-k):cl.append([-t,*[occ(v) for v in comb]])
    lower(ce,minimum-mins)
    ts=[]
    for v in range(512):
        n=[occ(v^(1<<d)) for d in range(9)];x=occ(v);t=513+v;ts.append(t)
        cl.append([-x,*n]);cl.append([-t,x])
        for i in range(9):cl.append([-x,t,*n[:i],*n[i+1:]])
        for c in itertools.combinations(n,3):cl.append([-x,*[-q for q in c]])
        for c in itertools.combinations(n,2):cl.append([-t,*[-q for q in c]])
    cl.extend(CardEnc.atmost(ts,2,vpool=vpool,encoding=EncType.seqcounter).clauses)
    for v in range(512):
        ds=[d for d in range(9) if not(v&(1<<d))]
        for i,j in itertools.combinations(ds,2):cl.append([-occ(v),-occ(v^(1<<i)),-occ(v^(1<<j)),-occ(v^(1<<i)^(1<<j))])
    with Cadical195(bootstrap_with=cl) as s:
        s.set_phases([occ(v) if v in p else -occ(v) for v in range(512)])
        cuts=0
        while True:
            rem=budget-s.accum_stats()['conflicts']
            if rem<=0:return dict(status='UNKNOWN',cuts=cuts)
            s.conf_budget(rem);r=s.solve_limited()
            if r is not True:return dict(status='UNSAT' if r is False else 'UNKNOWN',cuts=cuts,conflicts=s.accum_stats()['conflicts'])
            m=set(s.get_model());z={v for v in range(512) if occ(v) in m}
            assert len(z)>=minimum
            rem=set(z);cs=[]
            while rem:
                q=[rem.pop()]
                for x in q:
                    for d in range(9):
                        y=x^(1<<d)
                        if y in rem:rem.remove(y);q.append(y)
                cs.append(q)
            loops=[c for c in cs if all(sum((v^(1<<d)) in z for d in range(9))==2 for v in c)]
            if not loops:
                assert len(cs)==1;last=-1;v=next(x for x in z if sum((x^(1<<d)) in z for d in range(9))==1);path=[]
                while True:
                    path.append(v);ns=[v^(1<<d) for d in range(9) if (v^(1<<d)) in z and (v^(1<<d))!=last]
                    if not ns:break
                    last,v=v,ns[0]
                assert len(path)==len(z) and all(((x^path[j]).bit_count()==1)==(i==j-1) for j in range(len(path)) for i,x in enumerate(path[:j]))
                return dict(status='FOUND',witness=path)
            for c in loops:s.add_clause([-occ(v) for v in c]);cuts+=1
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('budget',type=int);ap.add_argument('--sample',type=int,default=1);a=ap.parse_args()
    jobs=[json.loads(l) for l in (D/'allpairs.jsonl').read_text().splitlines()]
    for c in jobs[::a.sample]:
        r=check(bank[c['source']],c['axes'],a.budget);r.update(id=c['id'],source=c['source'],axes=c['axes']);print(json.dumps(r),flush=True)
        if r['status']=='FOUND':break
