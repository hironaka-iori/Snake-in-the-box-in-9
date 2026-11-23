from collections import Counter,deque
from pathlib import Path
from itertools import accumulate
from operator import xor
import json,random,sys
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R))
from search_q9_anchored_sets import search
from search_q9_wynn_plateau import canonical,verify
rng=random.Random(182003)
def decode(w):return list(accumulate([1<<int(c) for c in w],xor,initial=0))
def rowword(p):return ''.join(str(x) for x in canonical(p))
def delete(p,step):
    rem=set(range(rng.randrange(0,13)))|set(range(len(p)-rng.randrange(1,15),len(p)))
    keep=rng.choice([108,119,132,143,153,165,174])
    mode=step%4
    while len(p)-len(rem)>keep:
        i=rng.randrange(len(p))
        if mode==0:rem.add(i);continue
        if mode==1:rem.update(range(i,min(len(p),i+rng.randint(1,8))));continue
        pivot=p[i];directions=rng.sample(range(9),rng.randrange(2,5));m=sum(1<<d for d in directions)
        cands=[j for j,v in enumerate(p) if (v^pivot).bit_count()<=2] if mode==2 else [j for j,v in enumerate(p) if (v^pivot)&~m==0]
        rem.update(cands)
    return {v for i,v in enumerate(p) if i not in rem}
def run():
    seed=decode((R/'q9_far_seedgrowth_20261121/new189.words').read_text().strip());assert verify(seed)
    known={k:{canonical(decode(w)) for w in (R/'q9_gap_generations'/f'prior{k}.words').read_text().split()} for k in [189,190,191]};known[189].add(canonical(seed));known[192]=set()
    group=[seed]; elite=[];got=set();counts=Counter();seen=set();queries=0
    for i in range(3200):
        p=seed if i%5==0 else rng.choice(elite or group)
        fixed=delete(p,i);key=frozenset(fixed)
        if key in seen:continue
        seen.add(key)
        for goal in [192,191,190]+([189] if i%7==0 else []):
            st,w=search(fixed,set(p),goal,12000 if i%9==0 else 3600,known=known[goal])
            counts[goal,st]+=1;queries+=1
            if w:
                assert verify(w) and len(w)==goal+1 and fixed<=set(w)
                c=canonical(w);assert c not in known[goal];known[goal].add(c);group.append(w)
                if goal>=190:elite.append(w)
                print(json.dumps(dict(i=i,goal=goal,w=rowword(w),parent=rowword(p),fixed=sorted(fixed))),flush=True)
                if goal==192:return
        # Positive progress: retain verified descendants for revisiting even when the
        # target class has already been catalogued.
        if i%13==0:
            st,w=search(fixed,set(p),190,2500)
            if w:
                assert verify(w);c=canonical(w)
                if c not in got:got.add(c);group.append(w);print(json.dumps(dict(known190=rowword(w),i=i)),flush=True)
    print(json.dumps(dict(done=queries,cores=len(seen),counts={str(k):v for k,v in counts.items()},any190=len(got))),flush=True)
if __name__=='__main__':run()
