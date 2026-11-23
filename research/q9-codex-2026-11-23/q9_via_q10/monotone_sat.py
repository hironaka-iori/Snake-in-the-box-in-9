from collections import Counter
from pathlib import Path
import json,random,sys
here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent))
from retry_q9_six_cube_sites_cadical import search
def check(w):
    assert len(w)==len(set(w)) and all(0<=x<512 for x in w)
    assert all((a^b).bit_count()==1 for a,b in zip(w,w[1:]))
    return [(i,j) for j,x in enumerate(w) for i,y in enumerate(w[:max(j-1,0)]) if (x^y).bit_count()==1]
def solve(n,seed):
    rng=random.Random(seed)
    src=(here/f'monotone_{n}.pts').read_text().splitlines()
    bank=[]
    for i,row in enumerate(src):
        p=list(map(int,row.split()))
        chords=check(p)
        if n>192 or len(chords)<=6:bank.append((i,p,chords))
    if n>192:bank=sorted(bank,key=lambda x:len(x[2]))[:90]
    stats=Counter();seen=set()
    for round in range(12):
        rng.shuffle(bank)
        for idx,p,chords in bank:
            cover=set()
            for i,j in rng.sample(chords,len(chords)):
                if not cover.intersection((i,j)):cover.add(rng.choice((i,j)))
            rad=2+(round%2)
            if round%3==1:
                fixed={p[j] for j in range(len(p)) if all(abs(j-i)>5+round for i in cover) and 3<j<len(p)-4}
            else:
                fixed={v for v in p if all((v^p[i]).bit_count()>rad for i in cover)}
                if round%3==2:fixed={v for v in fixed if min((v^p[0]).bit_count(),(v^p[-1]).bit_count())>2}
            code=frozenset(fixed)
            if not fixed or code in seen:continue
            seen.add(code)
            st,w=search(fixed,set(p),n,1400,set(range(512)));stats[st]+=1
            if w:
                assert len(w)>n and not check(w)
                print(json.dumps(dict(found=w,edges=len(w)-1,source=idx)),flush=True);return
            if sum(stats.values())%25==0:print(json.dumps(dict(tested=sum(stats.values()),counts=stats,round=round)),flush=True)
    print(json.dumps(dict(done=True,counts=stats,source_count=len(bank))),flush=True)
if __name__=='__main__':solve(int(sys.argv[1]),int(sys.argv[2]))
