"""Search Q9 with one affine patch released in an otherwise fixed parity half."""
from concurrent.futures import ProcessPoolExecutor
import json,random,sys
from search_q9_free_record_slice import parents,verify,search

def patch(seed,mask,side,rank,rng):
    generators=[x for x in range(1,512) if x.bit_count()<=2 and (x&mask).bit_count()%2==0]
    rng.shuffle(generators);span={0}
    for x in generators:
        if x in span:continue
        span|={v^x for v in span}
        if len(span)==1<<rank:break
    assert len(span)==1<<rank
    candidates=[v for v in seed if (v&mask).bit_count()%2==side]
    origin=rng.choice(candidates)
    return {origin^x for x in span}

def init():
    global bank
    bank=parents()
    for p in bank:verify(p)

def instance(i,mask,side,rank,salt,target,budget,at_least=False):
    p=bank[i];rng=random.Random(((i*521+mask)*31+side)*1237+salt)
    saved={v for v in p if (v&mask).bit_count()%2==side}
    edited=patch(p,mask,side,rank,rng)
    fixed=saved-edited
    allowed=fixed|edited|{v for v in range(512) if (v&mask).bit_count()%2!=side}
    st,w=search(fixed,set(p),target,budget,allowed=allowed,at_least=at_least)
    if w:
        verify(w);assert len(w)>=target+1 and (at_least or len(w)==target+1)
        assert ({v for v in w if (v&mask).bit_count()%2==side}^saved)<=edited
    return [i,mask,side,rank,salt,len(fixed),st,w]

def work(j):return instance(*j)

if __name__=="__main__":
    init()
    at_least="--at-least" in sys.argv
    jobs=[]
    masks=[x for x in range(1,512) if x.bit_count() in (7,8)]
    for i in range(len(bank)):
        rng=random.Random(862219+i)
        for m in rng.sample(masks,10):
            for s in (0,1):
                for n in (4,5,6):
                    jobs.append((i,m,s,n,19311+n,192,12000 if at_least else 5000,at_least))
    for i in (0,25,50,100):
        result=instance(i,511^1,i%2,4,19315,191,60000)
        assert result[6]!="UNSAT"
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for row in pool.map(work,jobs,chunksize=3):
            print(json.dumps(row,separators=(",",":")),flush=True)
            if row[-1]:break
