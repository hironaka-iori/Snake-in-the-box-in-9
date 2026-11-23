"""Merge near-contacts of non-touching paths or split long arcs while rerouting locally."""
from itertools import combinations
from pathlib import Path
from collections import Counter
import json,random,sys
from pysat.solvers import Minicard
from verify import valid,parse,shape
r=Path(__file__).resolve().parent
NB=[set(v^(1<<d) for d in range(8)) for v in range(256)]
def solve(paths,sites,rad,target,limits,dead,rng):
    F=set();ref=set(sum(paths,[]))
    for j,p in enumerate(paths):
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
                if shape(arms) not in old:return 'F',arms
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
    inp=Path(sys.argv[1]);target=int(sys.argv[2]);limit=int(sys.argv[3]);budget=int(sys.argv[4]);rng=random.Random(int(sys.argv[5]))
    pool=[parse(line) for line in inp.read_text().splitlines()]; old=set(map(lambda line:shape(parse(line)),(r/'ready.pts').read_text().splitlines())); counter=Counter()
    for rep in range(limit):
        paths=rng.choice(pool); ends=[(j,i,x) for j,p in enumerate(paths) for i,x in ((0,p[0]),(len(p)-1,p[-1]))]
        cand=sorted([((x^y).bit_count(),j,i,k,h,x,y) for j,i,x in ends for k,h,y in ends if j<k])
        dist,j,i,k,h,x,y=rng.choice(cand[:3]);sites=[(j,i),(k,h)]
        rad=rng.choice([4,5,6,7]);cross= (x^y)
        mids=[x^v for v in range(256) if not v&~cross and 0<(v.bit_count())<dist]
        hotspots=set(mids)|{x,y}
        for n,p in enumerate(paths):
            eligible=[(idx,z) for idx,z in enumerate(p) if min((z^m).bit_count() for m in hotspots)<=1]
            if n not in (j,k) and eligible:sites.append((n,rng.choice(eligible)[0]))
            if rep%3==0 and eligible:sites.append((n,rng.choice(eligible)[0]))
        if rep%2==0:
            l=rng.randrange(len(paths));sites.append((l,rng.choice((0,len(paths[l])-1))))
        st,p=solve(paths,sites,rad,target,(budget,18),[],rng);counter[st]+=1
        if p:old.add(shape(p));off=p[0][0];print(' '.join(' '.join(map(str,[len(a),*(z^off for z in a)])) for a in p),flush=True)
    print(dict(counter),file=sys.stderr)
if __name__=='__main__':main()
