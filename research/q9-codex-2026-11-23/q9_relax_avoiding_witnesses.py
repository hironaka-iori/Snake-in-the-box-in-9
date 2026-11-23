"""Resample spatial and temporal neighborhoods of verified outside-family snakes."""
import json,random
from search_q9_anchored_sets import search
from q9_avoiding_centers import reference,code
from search_q9_two_flexible_ends import verify
from search_q9_wynn_plateau import NB

def main():
    rng=random.Random(1890142);bank=reference(142)
    seeds=[list(map(int,l.split())) for l in open('q9_avoiding_mixed_paths.txt')]
    seeds.extend(r[2] for r in map(json.loads,open('q9_center_avoiding_seeds.jsonl')) if r[0]=='SEED')
    assert all(len(set(w))==len(w) for w in seeds)
    seen_shapes={code([a^b for a,b in zip(w,w[1:])]) for w in seeds}
    def forbidden(w):
        t=[x^y for x,y in zip(w,w[1:])]
        for i in range(len(w)-142):
            if code(t[i:i+142]) in bank:return w[i:i+143]
    for it in range(2200):
        p=rng.choice(seeds);base=set(p);free=set()
        for _ in range(rng.randrange(4,10)):
            pos=rng.randrange(len(p));rad=rng.randrange(3,9)
            free.update(p[max(0,pos-rad):pos+rad+1])
            if it%2:
                free.update(x for x in p if (x^p[pos]).bit_count()<=2)
        free.update(p[:rng.randrange(1,13)]);free.update(p[-rng.randrange(1,13):])
        forced=base-free
        if len(forced)<75:continue
        for n in (192,190):
            st,w=search(forced,base,n,4000,reject_fragment=forbidden)
            if w:
                verify(w,n);assert not forbidden(w)
                shape=code([x^y for x,y in zip(w,w[1:])])
                if shape not in seen_shapes:
                    seen_shapes.add(shape);seeds.append(w)
                    print(json.dumps(['SEED',it,n,w]),flush=True)
            print(json.dumps(['CHECK',it,n,st,len(forced)]),flush=True)
            if w and n==192:return
if __name__=='__main__':main()
