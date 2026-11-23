"""Move occupancy between two same-color pairs before freeing every pair orientation."""
import gzip
import json
import random
from verify_q9_center_avoidance import forms,verify
from q9_pair_selector import search

def main():
    bank={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192:bank.setdefault(forms(p,191)[0],p)
    hard={}
    for i,s,t,k,st,w in map(json.loads,open("q9_all_color_orbits_192.jsonl")):
        if st=="UNKNOWN":hard.setdefault((i,s),[]).append(t)
    axes=[t for t in range(1,512) if t.bit_count()==2]
    for i,p in enumerate(bank.values()):
        verify(p)
        for s in (0,1):
            rng=random.Random(837421+17*i+s)
            side=set(p[s::2])
            dirs={rng.choice(axes),rng.choice(hard.get((i,s),axes))}
            for t in sorted(dirs):
                def orb(v):return min(v,v^t)
                pop={v:len(side.intersection((v,v^t))) for v in range(512)
                     if v==orb(v) and not (v^p[s]).bit_count()%2}
                moves=set()
                while len(moves)<24:
                    v=rng.choice(list(pop))
                    y=orb(v^rng.choice(axes)) if rng.random()<0.5 else rng.choice(list(pop))
                    if v!=y and pop[v]>0 and pop[y]<2:moves.add((v,y))
                for v,y in sorted(moves):
                    trial=side-{next(w for w in (v,v^t) if w in side)}
                    trial.add(next(w for w in (y,y^t) if w not in side))
                    pairs=[(w,w^t) for w in sorted(trial) if w^t not in trial]
                    if len(pairs)==len(trial):continue
                    st,w=search(trial,pairs,t,set(p),192,4200)
                    if w:
                        verify(w);assert len(w)==193
                        b=set(w[1::2])
                        assert all(len(b.intersection((u,u^t)))==n-int(u==v)+int(u==y)
                                   for u,n in pop.items())
                    print(json.dumps([i,s,t,v,y,st,w],separators=(",",":")),flush=True)
                    if w:return

if __name__=="__main__":main()
