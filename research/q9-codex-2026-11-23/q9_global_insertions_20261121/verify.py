"""Validate full witnesses and independently solve fixed insertion-site refinements."""
import itertools, json, random, sys
from collections import Counter
from pathlib import Path
here=Path(__file__).resolve().parent;sys.path.insert(0,str(here.parent))
from repair_q9_time_projection import repair

def vertices(word):
    result=[0]
    for d in word:result.append(result[-1]^(1<<int(d)))
    return result
def check(p):
    return (len(set(p))==len(p) and all(0<=v<512 for v in p) and
        all(((a^b).bit_count()==1)==(i+1==j) for (i,a),(j,b) in itertools.combinations(enumerate(p),2)))
def expanded(seed,axes,extra,sites):
    src=iter(seed);wanted={k:(axes[0] if x<0 else x) for k,x in zip(sites,extra)}
    return ''.join(str(wanted[k]) if k in wanted else next(src) for k in range(len(seed)+len(extra)))
def fixed(seed,axes,extra,sites,budget):
    w=expanded(seed,axes,extra,sites);p=vertices(w);s,q=repair(p,axes,budget)
    if q:assert len(q)==len(w)+1 and check(q)
    return s
def validate(seed,axes,extra,sites,st,w):
    assert st=='FOUND' and len(w)==len(seed)+len(extra)+1 and check(w)
    p=vertices(expanded(seed,axes,extra,sites));mask=sum(1<<d for d in axes)
    assert all((v&~mask)==(u&~mask) for v,u in zip(w,p))
def main():
    bank={L:(here.parent/f'q9_gap_generations/prior{L}.words').read_text().splitlines() for L in (190,191)}
    assert all(check(vertices(w)) for pool in bank.values() for w in pool)
    for S,row,planted,seed,a,e,st,c,sites,w in map(json.loads,(here/'controls.jsonl').read_text().splitlines()):
        assert check(vertices(seed)) and check(vertices(bank[191][row]))
        validate(seed,a,e,sites,st,w)
        alt=fixed(seed,a,e,sites,120000)
        print(json.dumps(['control',S,planted,sites,alt]),flush=True)
    rng=random.Random(3821)
    # The zero-base and nonzero-base single-insertion cases each receive an
    # exhaustive replay of all 192 possible output transition positions.
    for L in (191,190):
        rows=[]
        for f in sorted(here.glob(f'run{L}_*.jsonl')):
            rows.extend(json.loads(l) for l in f.read_text().splitlines())
        for r in rows:
            if r[4]=='FOUND':validate(bank[L][r[1]],r[2],r[3],r[6],r[4],r[7])
        groups={}
        for i,row,ax,e,st,c,_,_ in rows:
            kind=tuple(x<0 for x in e)
            if st=='UNSAT' and kind not in groups:groups[kind]=(row,ax,e)
        for kind,(row,a,e) in groups.items():
            possibilities=list(itertools.combinations(range(192),192-L))
            if L==190:possibilities=rng.sample(possibilities,128)
            tally=Counter()
            for sites in possibilities:
                st=fixed(bank[L][row],a,e,sites,12000);tally[st]+=1
                if st=='FOUND':raise RuntimeError((L,row,a,e,sites))
            print(json.dumps([L,row,a,e,len(possibilities),dict(tally)]),flush=True)
if __name__=='__main__':main()
