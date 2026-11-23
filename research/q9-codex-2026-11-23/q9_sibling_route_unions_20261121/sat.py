"""Occupancy SAT. Local alternative edges and time positions are not imposed."""
from itertools import combinations
from collections import Counter
from pysat.solvers import Minicard
import json,sys,random
from build import D,N
def solve(pool,fixed,raw,size,budget,majority,required_groups=()):
    fixed=set(fixed);S=set(raw);pool=set(pool)
    packed={v for v in fixed if sum(u in fixed for u in N[v])>=2}
    pool-=set().union(*(set(N[v]) for v in packed))-fixed if packed else set()
    if len(pool)<size:return dict(status='UNSAT',conflicts=0,cuts=0,domain=len(pool),path=None)
    degs={v:set(N[v])&pool for v in pool}
    with Minicard() as solver:
        add=solver.add_clause
        def eq(ls,n):
            if not 0<=n<=len(ls):add([]);return
            if n<len(ls):solver.add_atmost(ls,n)
            if n:solver.add_atmost([-x for x in ls],len(ls)-n)
        for x in fixed:add([x+1])
        for f in required_groups:add([v+1 for v in f if v in pool])
        for v,nei in degs.items():
            e=v+513;add([-e,v+1]);need=2-len(nei&fixed);ls=[u+1 for u in nei-fixed]+[e]
            if not 0<=need<=len(ls):add([-v-1]);continue
            for xx in combinations(ls,need+1):add([-v-1,*(-x for x in xx)])
            for xx in combinations(ls,len(ls)-need+1):add([-v-1,*xx])
        for color in (0,1):
            part={v for v in pool if v.bit_count()%2==color};n=size//2+int(size%2 and color==majority)
            eq([v+1 for v in part-fixed],n-len(part&fixed))
            eq([v+513 for v in part],(2*int(color==majority)) if size%2 else 1)
        solver.set_phases([v+1 if v in S else -v-1 for v in pool]);cuts=0
        while (remaining:=budget-solver.accum_stats()['conflicts'])>0:
            solver.conf_budget(remaining);ok=solver.solve_limited()
            if ok is not True:break
            model=set(solver.get_model());sel={v for v in pool if v+1 in model};unseen=set(sel);route=[]
            while unseen:
                comp=[unseen.pop()]
                for v in comp:
                    new=degs[v]&unseen;unseen-=new;comp.extend(new)
                ends=[v for v in comp if len(degs[v]&sel)==1]
                if not ends:
                    add([-v-1 for v in comp if v not in fixed]);cuts+=1;continue
                assert len(ends)==2;route=[ends[0]];prev=None
                while route[-1]!=ends[1]:
                    v=route[-1];u,=degs[v]&sel-{prev};route.append(u);prev=v
            if len(route)==size:
                assert fixed<=set(route)<=pool and set(route)==sel;break
        else:ok=None
        return dict(status='FOUND' if ok is True else 'UNSAT' if ok is False else 'LIMIT',conflicts=solver.accum_stats()['conflicts'],cuts=cuts,domain=len(pool),path=route if ok is True else None)
def mode_args(r,mode,control):
    base=set(r['raw']);hard=set(r['hard']);groups=[set(g['extra']) for g in r['groups']]
    ids=[i for i,g in enumerate(groups) if g]
    if mode=='single':
        for i in ids:yield str(i),base|groups[i],hard,[]
    else:
        pool=base|set().union(*groups);known=r['changed']
        if mode!='tight':
            radius=4 if mode=='loose' else 9
            pos={k for a,b in r['holes'] for k in (a,b)}
            hard-={v for j,v in enumerate(r['raw']) if min(abs(j-h) for h in pos)<=radius}
        required=[]
        if mode=='joint':
            singles=[g-set().union(*(m for m in groups if m is not g)) for g in groups]
            required=sorted((s for s in singles if s),key=len,reverse=True)[:2]
            if len(required)<2:return
        yield mode,pool,hard,required
def main():
    src,mode,cap,limit=sys.argv[1:5];control=src.startswith('control');cnt=0
    for line in (D/(src+'.pools')).open():
        r=json.loads(line)
        for key,pool,hard,req in mode_args(r,mode,control):
            for col in ([None] if control else [r['raw'][0].bit_count()%2,1-r['raw'][0].bit_count()%2]):
                z=solve(pool,hard,r['raw'],len(r['raw']),int(cap),col,req)
                z.update(src=r['src'],version=r['version'],mode=key,hard=len(hard),union=len(pool),majority=col)
                print(json.dumps(z,separators=(',',':')),flush=True);cnt+=1
                if z['path'] and not control:return
                if cnt>=int(limit):return
if __name__=='__main__':main()
