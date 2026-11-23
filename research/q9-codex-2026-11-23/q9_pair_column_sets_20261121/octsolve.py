from pathlib import Path
import argparse,gzip,itertools,json,random,sys
from collections import Counter
from pysat.solvers import Minicard
D=Path(__file__).resolve().parent
R=D.parent
cube=set(range(512))
NB=[tuple(v^(1<<d) for d in range(9)) for v in range(512)]
bank=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')]
def verify(p):
    assert len(set(p))==len(p) and min(p)>=0 and max(p)<512
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p[i+1:],i+1))
def col(v,a):return v&~(1<<a)
def split(p,a):return {col(x,a) for x in p}
def case(i):
    rng=random.Random(191005541+i)
    k=i%len(bank);p=bank[k];aa=rng.sample(range(9),2);A,B=aa;mode=(i//len(bank))%4
    bases={col(col(v,A),B) for v in cube}
    if mode==0:
        size=(10,19,35,54)[k%4];base=rng.sample(sorted(bases),size); U=set(base)
        patches=[{col(x,a) for v in U for x in (v,v^(1<<A),v^(1<<B),v^(1<<A)^(1<<B))} for a in aa]
    elif mode==1:
        size=(28,42,64,88)[k%4];patches=[set(rng.sample(sorted(split(cube,a)),size)) for a in aa]
    elif mode==2:
        pick=[p[rng.randrange(192)] for _ in range((2,3,4,5)[k%4])]
        U={col(col(v,A),B) for b in pick for v in (b,*NB[b])}
        patches=[{col(x,a) for v in U for x in (v,v^(1<<A),v^(1<<B),v^(1<<A)^(1<<B))} for a in aa]
    else:
        half=set(rng.sample(sorted(bases),64));extra=set(rng.sample(sorted(bases),(0,8,20,32)[k%4]))
        patches=[{v for v in split(cube,a) if col(col(v,A),B) in H|extra} for a,H in zip(aa,(half,bases-half))]
    return p,aa,patches,k,mode
def solve(p,aa,patches,n,limit,require_new=True,hint=None,pin=None,base_override=None):
    cols=[split(cube,a) for a in aa];base=base_override if base_override is not None else [split(p,a) for a in aa]
    need=[s-u for s,u in zip(base,patches)]
    allowed={x for x in cube if all(col(x,a) in f|u for a,f,u in zip(aa,need,patches))}
    fixed=set()
    for a,f in zip(aa,need):
        for v in f:
            opts={v,v^(1<<a)}&allowed
            if not opts:return dict(status='EMPTY')
            if len(opts)==1:fixed.update(opts)
    if len(allowed)<n:return dict(status='SIZE')
    with Minicard() as s:
        def atmost(ls,k):
            if k<0:s.add_clause([])
            elif k<len(ls):s.add_atmost(ls,k)
        def least(ls,k):atmost([-x for x in ls],len(ls)-k)
        def exact(ls,k):least(ls,k);atmost(ls,k)
        for x in fixed:s.add_clause([x+1])
        for x in cube-allowed:s.add_clause([-x-1])
        if pin is not None:
            for x in pin:s.add_clause([x+1])
        for j,(a,U,F,orig) in enumerate(zip(aa,patches,need,base)):
            opt=[];doubles=[];par={0:[],1:[]}
            def occ(t):return 1100+j*1024+t
            def dbl(t):return 1612+j*1024+t
            for v in sorted(U|F):
                endpoints=[x+1 for x in (v,v^(1<<a)) if x in allowed]
                if v in F:s.add_clause(endpoints)
                else:
                    o=occ(v);opt.append(o);par[v.bit_count()%2].append(o)
                    for l in endpoints:s.add_clause([-l,o])
                    s.add_clause([-o,*endpoints])
                if len(endpoints)!=2:continue
                adjcol=[v^(1<<d) for d in range(9) if d!=a]
                mandatory=sum(t in F for t in adjcol)
                if mandatory>=3:
                    s.add_clause([-l for l in endpoints]);continue
                t=dbl(v);doubles.append(t)
                for l in endpoints:s.add_clause([-t,l])
                s.add_clause([t,*[-l for l in endpoints]])
                for group in itertools.combinations([q for q in adjcol if q in U],3-mandatory):
                    s.add_clause([-t,*[-occ(q) for q in group]])
            least(opt+doubles,n-len(F))
            if require_new:s.add_clause([-occ(t) if t in orig else occ(t) for t in U])
            delta=sum(1 if t.bit_count()%2==0 else -1 for t in F)
            vals=par[0]+[-t for t in par[1]]
            least(vals,len(par[1])-delta-1);atmost(vals,len(par[1])-delta+1)
        for x in allowed:
            for d,e in itertools.combinations(range(9),2):
                if x&(1<<d) or x&(1<<e):continue
                square=(x,x^(1<<d),x^(1<<e),x^(1<<d)^(1<<e))
                if all(y in allowed for y in square):s.add_clause([-y-1 for y in square])
        for parity in (0,1):
            bits=[x+1 for x in allowed if x.bit_count()%2==parity]
            least(bits,n//2)
        extra=[];minimum=0
        A,B=aa
        for g in sorted({col(col(x,A),B) for x in cube}):
            cell=[g,g^(1<<A),g^(1<<B),g^(1<<A)^(1<<B)]
            subsets=[]
            for mask in range(15):
                z={x for j,x in enumerate(cell) if mask>>j&1}
                if z<=allowed and all(need[j]&split(cell,a)<=split(z,a) for j,a in enumerate(aa)):
                    subsets.append(z)
            if not subsets:s.add_clause([]);continue
            lo=min(map(len,subsets));hi=max(map(len,subsets));minimum+=lo
            vs=[x+1 for x in cell if x in allowed]
            for amount in range(lo+1,hi+1):
                u=4000+4*g+amount;extra.append(u)
                for comb in itertools.combinations(vs,amount):s.add_clause([u,*[-t for t in comb]])
                for comb in itertools.combinations(vs,len(vs)-amount+1):s.add_clause([-u,*comb])
        least(extra,n-minimum)
        from octagons import cycles
        for clause in cycles(tuple(i for i in range(9) if i not in aa)):s.add_clause(clause)
        ends=[];majority=3500
        for x in allowed:
            X=x+1;e=513+x;ends.append(e)
            neighbors=[v+1 for v in NB[x] if v in allowed]
            s.add_clause([-e,X]);s.add_clause([-X,*neighbors])
            for l in itertools.combinations(neighbors,3):s.add_clause([-X,*[-u for u in l]])
            for a,b in itertools.combinations(neighbors,2):s.add_clause([-e,-a,-b])
            for j in range(len(neighbors)):s.add_clause([-X,e,*neighbors[:j],*neighbors[j+1:]])

        exact(ends,2)
        h=set(p if hint is None else hint);s.set_phases([x+1 if x in h else -x-1 for x in allowed])
        cuts=0
        while True:
            used=s.accum_stats()['conflicts']
            if used>=limit:status='UNKNOWN';break
            s.conf_budget(limit-used);ok=s.solve_limited()
            if ok is not True:status='UNKNOWN' if ok is None else 'UNSAT';break
            model=set(s.get_model());chosen={x for x in allowed if x+1 in model};assert len(chosen)>=n
            remain=set(chosen);comps=[]
            while remain:
                q=[remain.pop()]
                for v in q:
                    for t in NB[v]:
                        if t in remain:remain.remove(t);q.append(t)
                comps.append(q)
            if len(comps)==1:
                dist={v:set(NB[v])&chosen for v in chosen};st=next(v for v in chosen if len(dist[v])==1);w=[st]
                while rem:=dist[w[-1]]-set(w):w.append(rem.pop())
                assert len(w)>=n;verify(w)
                assert all(split(w,a)-u==t-u for a,u,t in zip(aa,patches,base))
                if require_new:assert all(split(w,a)!=t for a,t in zip(aa,base))
                return dict(status='FOUND',witness=w,fixed=len(fixed),pool=len(allowed),cuts=cuts,conflicts=s.accum_stats()['conflicts'])
            for comp in comps:
                if all(sum(t in chosen for t in NB[v])==2 for v in comp):
                    s.add_clause([-v-1 for v in comp]);cuts+=1
        return dict(status=status,fixed=len(fixed),pool=len(allowed),cuts=cuts,conflicts=s.accum_stats()['conflicts'])
def main():
    ap=argparse.ArgumentParser();ap.add_argument('start',type=int);ap.add_argument('stop',type=int);ap.add_argument('budget',type=int);ap.add_argument('--prior');args=ap.parse_args()
    keys=range(args.start,args.stop) if not args.prior else [r['id'] for l in Path(args.prior).read_text().splitlines() if (r:=json.loads(l)).get('status')=='UNKNOWN']
    for i in keys:
        p,aa,us,k,mode=case(i);r=solve(p,aa,us,193,args.budget)
        r.update(id=i,source=k,axes=aa,mode=mode,free=list(map(len,us)));print(json.dumps(r,separators=(',',':')),flush=True)
        if r['status']=='FOUND':break
if __name__=='__main__':main()
