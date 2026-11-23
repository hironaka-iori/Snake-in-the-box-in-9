import argparse,collections,gzip,itertools,json,random,sys,time
from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc
D=Path(__file__).resolve().parent;R=D.parent
P=[v for v in range(512) if v.bit_count()%2==0];O=sorted(set(range(512))-set(P))
N=[[v^(1<<i) for i in range(9)] for v in range(512)]
M=[(1<<i)|(1<<j) for j in range(9) for i in range(j)]
def validate(p):
    return len(p)==len(set(p)) and all(((x^y).bit_count()==1)==(j+1==i) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
def shade(p):
    return [v^(p[0].bit_count()%2) for v in p]
def score(s):
    deg=collections.Counter()
    for o in O:
        vs=[v for v in N[o] if v in s]
        if len(vs)==2:deg.update(vs)
    return sum(9*(deg[x]==0)+2*(deg[x]==1) for x in s)
def tree_sources(rng,count,n=97):
    ws=(R/'q8_catalogue_96_98.words').read_text().split()
    keep=[]
    for i in range(count):
        word=rng.choice(ws);vertices=list(range(9));rng.shuffle(vertices);masks=[(1<<vertices[j])^(1<<vertices[rng.randrange(j)]) for j in range(1,9)];rng.shuffle(masks)
        x=0;s={0}
        for c in word[:n-1]:x^=masks[int(c)];s.add(x)
        assert len(s)==n
        keep.append((score(s),i,sorted(s),masks,word[:n-1]))
    return sorted(keep)
class Formula:
    def __init__(self):self.n=0;self.cs=[]
    def var(self):self.n+=1;return self.n
    def clause(self,cl):
        if any(x is True for x in cl):return
        s={x for x in cl if x is not False}
        if not any(-x in s for x in s):self.cs.append(list(s))
    def cap(self,terms,maxv,guard=()):
        q=maxv-sum(x is True for x in terms)
        lits=[x for x in terms if type(x) is int]
        if q<0:self.clause(guard)
        elif q<len(lits):
            for a in itertools.combinations(lits,q+1):self.clause([*guard,*(-x for x in a)])
    def minimum(self,terms,k,guard=()):
        self.cap([neg(x) for x in terms],len(terms)-k,guard)
    def equals(self,ls,k):
        enc=CardEnc.equals(lits=ls,bound=k,top_id=self.n,encoding=1);self.n=max(self.n,enc.nv);self.cs.extend(enc.clauses)
def neg(x):return not x if type(x) is bool else -x
def solve(s,m,free,minimum,budget,seed,root,extra,cutlimit,globaladd=False,maxmove=None,cloud=None):
    f=Formula();ev={x:(x in s) for x in P};flips=[]
    for a,b in free:
        assert a in s and b not in s and a!=b
        z=f.var();flips.append(z);ev[a]=-z;ev[b]=z
    if cloud is not None:
        assert not free
        terms=[];lost=0
        for v in sorted(cloud):
            u=f.var();ev[v]=u;terms.append(u)
            if v in s:flips.append(-u);lost+=v in s
        if globaladd:
            outside=[]
            for v in P:
                if v not in s and v not in cloud:
                    u=f.var();ev[v]=u;outside.append(u)
            flag=f.var();terms.append(flag)
            # Choosing exactly one outside point or choosing none and the flag complement.
            f.equals(outside+[-flag],1)
        f.equals(terms,lost+int(globaladd))
    elif globaladd:
        added=[];paired=set()
        for a,b in free:
            old=ev[a];new=f.var();y=f.var();ev[b]=new;paired.update((a,b))
            f.clause([old,new]);f.clause([-y,old]);f.clause([-y,new]);f.clause([neg(old),-new,y]);added.append(y)
        for v in P:
            if v not in s and v not in paired:u=f.var();ev[v]=u;added.append(u)
        f.equals(added,1)
    if maxmove is not None:f.cap(flips,maxmove)
    if len(flips)<minimum:return dict(status='empty')
    if minimum:
        enc=CardEnc.atleast(lits=flips,bound=minimum,top_id=f.n,encoding=1);f.n=enc.nv;f.cs+=enc.clauses
    od={}
    for w in O:
        adj=[ev[v] for v in N[w]];fixed=sum(v is True for v in adj);possible=sum(v is not False for v in adj)
        if fixed>2 or possible<2:od[w]=False;continue
        y=f.var();od[w]=y;f.cap(adj,2,[-y]);f.minimum(adj,2,[-y])
    eps=[]
    for x,on in ev.items():
        if on is False:continue
        op=[od[w] for w in N[x] if od[w] is not False];g=[neg(on)]
        f.minimum(op,1,g);f.cap(op,2,g);e=f.var();eps.append(e);f.clause([-e,on]);f.minimum(op,2,[*g,e]);f.cap(op,1,[-e])
    f.equals(eps,2)
    # The endpoints are both even. Sum of degrees implies exactly |S|-1 selected odd vertices.
    variables={**ev,**od};result=dict(free=len(flips),nvar=f.n,nclauses=len(f.cs),cuts=0,root=root,extra=extra,score=score(s),mask=m)
    with Solver(name='g4',bootstrap_with=f.cs) as slv:
        while result['cuts']<=cutlimit:
            slv.conf_budget(budget);ans=slv.solve_limited();stat=slv.accum_stats();result['conflicts']=stat['conflicts']
            if ans is not True:return dict(result,status='UNSAT' if ans is False else 'BUDGET')
            mdl=set(slv.get_model());used={v for v,on in variables.items() if on is True or type(on) is int and on in mdl}
            assert len(used)==2*(len(s)+int(globaladd))-1
            start=next(v for v in used if sum(x in used for x in N[v])==1);path=[];before=-1;v=start
            while True:
                path.append(v);nxt=[x for x in N[v] if x!=before and x in used]
                if not nxt:break
                assert len(nxt)==1;before,v=v,nxt[0]
            if len(used)==len(path):
                assert validate(path);return dict(result,status='FOUND',moves=len(s-set(path)),path=path)
            comp=set(path);outside=used-comp;ref=next(iter(outside));inside=next(iter(comp));boundary={v for u in comp for v in N[u] if v not in comp}
            cl=[neg(variables[inside]),neg(variables[ref]),*(variables[v] for v in boundary)];assert all(v is not True for v in cl)
            slv.add_clause(list({v for v in cl if v is not False}));result['cuts']+=1
    return dict(result,status='CUT_BUDGET')
def match(s,m):return [(a,a^m) for a in sorted(s) if (a^m) not in s]
def main():
    ap=argparse.ArgumentParser();ap.add_argument('mode');ap.add_argument('count',type=int);ap.add_argument('seed',type=int);ap.add_argument('budget',type=int);ap.add_argument('--tree-length',type=int,default=97);args=ap.parse_args();rng=random.Random(args.seed);paths=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')]
    tree=json.loads((D/'ranked.json').read_text()) if args.mode.startswith('ranked') else tree_sources(rng,1800,args.tree_length)[:45] if args.mode.startswith('tree') else []
    if args.mode.startswith("near"):
        near=set()
        for line in (R/"q9_rotate_fragments_20261121/bank.txt").read_text().splitlines():
            q=shade(list(map(int,line.split())));v=tuple(sorted(set(q[::2])))
            if len(v)==97:near.add(v)
        tree=[[score(set(z)),i,z,None,None] for i,z in enumerate(sorted(near))]
        tree.sort()
    if tree:(D/(args.mode+'_sources.json')).write_text(json.dumps(tree))
    for i in range(args.count):
        m=rng.choice(M);idx=rng.randrange(len(paths));extra=None
        p=shade(paths[idx] if rng.randrange(2) else paths[idx][::-1]);s=set(p[::2])
        if args.mode.startswith('control'):
            missing=None
            if args.mode=='controlgain':missing=p[2*rng.randrange(len(p)//2)];s.remove(missing)
            pl=[q for q in match(s,m) if missing not in q];rng.shuffle(pl);d=2+i%5
            for a,b in pl[:d]:s.remove(a);s.add(b)
            free=[(b,a) for a,b in pl[:d]]+pl[d:d+15];minimum=d
        elif args.mode.startswith('gain'):
            free=match(s,m);minimum=2
        elif tree:
            rank=i%len(tree);sc,idx,orig,*_=tree[rank];s=set(orig);free=match(s,m);minimum=2
        else:
            candidates=[x for x in P if x not in s];rng.shuffle(candidates);candidates=candidates[:20];extra=min(candidates,key=lambda x:score(s|{x}));s.add(extra);free=match(s,m);minimum=2
        if args.mode.endswith('mixed') or "varied" in args.mode:
            # Replace up to half of the common-axis pairs by a disjoint local matching in other directions.
            rng.shuffle(free);fixed=free[:len(free)//2];used={v for t in fixed for v in t};z=[v for v in s if v not in used];rng.shuffle(z)
            for a in z:
                opts=[a^q for q in M if (a^q) not in s and (a^q) not in used]
                if opts:b=rng.choice(opts);fixed.append((a,b));used.update((a,b))
            free=fixed
        if args.mode.endswith("local"):
            rng.shuffle(free);free=free[:[19,30,43,55][i%4]]
        maxmove=1 if args.mode=="control1" else None
        if maxmove is not None:minimum=0
        out=solve(s,m,free,minimum,args.budget,args.seed,idx,extra,20,(args.mode.startswith("gain") or args.mode=="controlgain"),maxmove);out.update(i=i,mode=args.mode,minimum=minimum)
        print(json.dumps(out,separators=(',',':')),flush=True)
        if not args.mode.startswith('control') and out['status']=='FOUND':break
if __name__=='__main__':main()
