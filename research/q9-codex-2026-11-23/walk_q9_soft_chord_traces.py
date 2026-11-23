"""Move the chord of an almost-induced path while preserving a coarse transition sequence."""
import json,random,sys,time
from collections import Counter
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
from explore_q9_one_chord_block_lifts import key,endpoint_extensions
from lift_q9_soft_chords import soft_build
from repair_q9_time_projection import valid

def detect(q):
    ix={v:i for i,v in enumerate(q)}
    assert len(ix)==len(q)==193 and all((x^y).bit_count()==1 for x,y in zip(q,q[1:]))
    return [(i,j) for i,x in enumerate(q) for b in range(9) if (j:=ix.get(x^1<<b,-1))>i+1]
def sample(p,groups,r,free,old,cap,budget):
    built=soft_build(p,groups,r,free,old,cap)
    if built is None:return
    cls,hints,rows,pars,tables,soft,last=built
    if len(soft)>cap:cls.extend(CardEnc.atmost(soft,cap,top_id=last,encoding=EncType.seqcounter).clauses)
    with Solver(name='cadical195',bootstrap_with=cls) as sat:
        sat.set_phases(hints+[-x for x in soft])
        sat.conf_budget(budget)
        if sat.solve_limited() is not True:return
        model=set(sat.get_model());q=[]
        for row,par in zip(rows,pars):
            x=0
            for j,v in enumerate(row):
                a=v if type(v) is int else next(i for i,b in enumerate(v) if b in model)
                x|=tables[j][(par>>j)&1,a]
            q.append(x)
        return q
def main():
    init,known_file,minutes,seed=sys.argv[1:5];rng=random.Random(int(seed))
    old191={key(list(map(int,l.split()))) for l in Path(known_file).read_text().splitlines()};assert len(old191)==131
    sets=[[],[],[],[]];seen=set();stats=Counter()
    for line in Path(init).read_text().splitlines():
        p=list(map(int,line.split()));bad=detect(p);assert len(bad)==1;k=key(p)
        if k not in seen:seen.add(k);sets[1].append((p,bad))
    start=last=time.monotonic();trials=0
    while time.monotonic()<start+60*float(minutes):
        trials+=1
        level=rng.choice([i for i in (1,1,2,2,3) if sets[i]])
        p,bad=rng.choice(sets[level]);old=rng.choice(bad)
        cap=rng.choice([0,1,1,2,2,2,3]) if level<3 else rng.choice([1,2,2,3])
        axes=list(range(9));rng.shuffle(axes);groups=[]
        for n in rng.choice([(3,3,3),(3,2,2,2),(3,3,2,1),(2,2,2,2,1)]):
            groups.append(axes[:n]);axes=axes[n:]
        q=sample(p,groups,rng,rng.choice([.12,.2,.31,.43,.56,.70]),old,cap,rng.choice([200,450,900]))
        if q:
            d=detect(q);assert len(d)<=cap and old not in d;stats['model']+=1
            if not d:
                assert valid(q);print(json.dumps(['FOUND192',q]),flush=True);return
            k=key(q);e=len(d)
            if k not in seen:
                seen.add(k);stats['new'+str(e)]+=1
                if len(sets[e])<20000:sets[e].append((q,d))
                elif rng.randrange(3)==0:sets[e][rng.randrange(len(sets[e]))]=(q,d)
                if e==1:
                    print(json.dumps(['E1',k.hex(),d]),flush=True)
                    for v,seg in [(0,q[1:]),(192,q[:-1])]:
                        if v not in d[0]:continue
                        assert valid(seg);code=key(seg)
                        if code not in old191:
                            old191.add(code);print(json.dumps(['NEW191',seg]),flush=True)
                            w=endpoint_extensions(seg)
                            if w:print(json.dumps(['FOUND192',w]),flush=True);return
        if time.monotonic()>last+60:
            print(json.dumps(['STATUS',trials,list(map(len,sets)),stats]),flush=True);last=time.monotonic()
    print(json.dumps(['DONE',trials,list(map(len,sets)),stats]),flush=True)
if __name__=='__main__':main()
