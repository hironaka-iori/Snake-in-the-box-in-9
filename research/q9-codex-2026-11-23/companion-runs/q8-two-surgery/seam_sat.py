"""Merge near-contacts of non-touching paths or split long arcs while rerouting locally."""
from itertools import combinations
from pathlib import Path
from collections import Counter
import json,random,sys
from pysat.solvers import Minicard
from verify import valid,parse,shape
r=Path(__file__).resolve().parent
NB=[set(v^(1<<d) for d in range(8)) for v in range(256)]
def solve(a,b,sites,rad,target,limits,dead,rng):
    F=set();ref=set(a+b)
    for j,p in enumerate([a,b]):
        for i,x in enumerate(p):
            if all(abs(k-i)>rad for pos,k in sites if j==pos):
                F.add(x)
    F-=set(dead)
    ds=[len(ns&F) for ns in NB];sat2={x for x in F if ds[x]==2}
    free={x for x in range(256) if x not in F and x not in dead and ds[x]<=2 and not NB[x]&sat2}
    if target-len(F)>len(free):return 'U',None
    with Minicard() as s:
        def exactly(xs,k):
            if k<0 or k>len(xs):s.add_clause([]);return
            s.add_atmost(xs,k);s.add_atmost([-t for t in xs],len(xs)-k)
        exactly([x+1 for x in free],target-len(F))
        es=[]
        for x in F|free:
            if x in sat2:continue
            guard=[] if x in F else [-x-1];e=x+257;es.append(e)
            if guard:s.add_clause([-e,x+1])
            opts=[y+1 for y in (NB[x]&free)]+[e];k=2-ds[x]
            if k>len(opts):s.add_clause(guard);continue
            for ys in combinations(opts,k+1):s.add_clause(guard+[-z for z in ys])
            for ys in combinations(opts,len(opts)-k+1):s.add_clause(guard+list(ys))
        exactly(es,4)
        s.set_phases([x+1 if x in ref else -x-1 for x in free])
        for it in range(limits[1]):
            left=limits[0]-s.accum_stats()['conflicts']
            if left<=0:return '?',None
            s.conf_budget(left);status=s.solve_limited()
            if status is not True:return ('?' if status is None else 'U'),None
            model=set(s.get_model());S=F|{x for x in free if x+1 in model};other=set(S);arms=[]
            for x in list(S):
                if x not in other or len(NB[x]&S)!=1:continue
                t=[x];other.remove(x)
                while NB[t[-1]]&other:
                    y,=NB[t[-1]]&other;t.append(y);other.remove(y)
                arms.append(t)
            if len(arms)==2 and not other:
                valid(arms);assert sum(map(len,arms))==target
                if sorted(map(len,arms))!=sorted([len(a),len(b)]) or shape(arms) not in old:return 'F',arms
                s.add_clause([-x-1 for x in S-F])
            else:
                assert len(arms)==2 and other
                while other:
                    block=[other.pop()]
                    for x in block:
                        for y in NB[x]&other:other.remove(y);block.append(y)
                    s.add_clause([-v-1 for v in block if v not in F])
        return '?',None

def main():
    global old
    inp=Path(sys.argv[1]);target=int(sys.argv[2]);rad=int(sys.argv[3]);limit=int(sys.argv[4]);seed=int(sys.argv[5]);budget=int(sys.argv[6])
    rng=random.Random(seed);pool=[parse(l) for l in inp.read_text().splitlines()];old=set(map(shape,pool));counter=Counter()
    for rep in range(limit):
        a,b=rng.choice(pool[:min(len(pool),250)])
        j,k=rng.choice([(i,j) for i,x in enumerate(a) for j,y in enumerate(b) if (x^y).bit_count()<=3])
        # Delete at least one old vertex. Free selected windows from both arms,
        # including an optional endpoint or another interval to shift component length.
        pairs=[(0,j),(1,k)]
        if rep%3:pairs.append(rng.choice([(0,0),(0,len(a)-1),(1,0),(1,len(b)-1)]))
        if rep%4==0:pairs.extend([(0,rng.randrange(len(a))),(1,rng.randrange(len(b)))])
        kill=[rng.choice([a[j],b[k]])]
        st,p=solve(a,b,pairs,rad,target,(budget,18),kill,rng);counter[st]+=1
        if p:
            key=shape(p)
            if key in old:continue
            old.add(key);pool.append(p);corner=p[0][0]
            print(' '.join(' '.join(map(str,[len(w),*(v^corner for v in w)])) for w in p),flush=True)
    print(dict(counter),file=sys.stderr)
if __name__=='__main__':main()
