from collections import Counter
import json,sys
from itertools import combinations
from pathlib import Path
here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent))
from search_q9_time_vertex_lists import solve_domains

def chords(p):
    assert all(0<=v<512 for v in p) and len(set(p))==len(p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return [(i,j) for (i,a),(j,b) in combinations(enumerate(p),2) if j>i+1 and (a^b).bit_count()==1]

def signature(v,axes,phase):
    return tuple(((v^phase)&m).bit_count() for m in axes)
def solve_independent(p,axes,phase,budget):
    domain={}
    for v in range(512):domain.setdefault(signature(v,axes,phase),set()).add(v)
    return solve_domains(p,[domain[signature(x,axes,phase)] for x in p],budget)
def main():
    bank=[list(map(int,line.split())) for line in (here.parent/'q9_onechord_expanded_800.txt').read_text().splitlines()]
    assert len(bank)==800 and all(len(p)==193 and len(chords(p))==1 for p in bank)
    control=json.loads((here/'control.json').read_text());p=control['damaged'];w=control['witness'];ax=control['masks'];phase=control['gauge']
    assert len(p)==len(w)==192 and chords(p) and not chords(w)
    assert list(map(lambda v:signature(v,ax,phase),p))==list(map(lambda v:signature(v,ax,phase),w))
    status,w2=solve_independent(p,ax,phase,15000)
    assert status=='FOUND' and len(w2)==192 and not chords(w2)
    print('verified 800 one-chord inputs; planted damage has',len(chords(p)),'chords; both encodings recover 191')
    for log in sorted(here.glob('shape*.jsonl')):
        records=[json.loads(l) for l in log.read_text().splitlines()];stats=Counter(r[4] for r in records)
        sample=[r for r in records if r[4]=='UNSAT'][:16]
        checked=Counter()
        for _,row,axes,phase,status,c,_ in sample:
            other,w=solve_independent(bank[row],axes,phase,8000)
            if other=='FOUND':raise AssertionError((row,axes,phase,w))
            checked[other]+=1
        for _,row,axes,phase,status,c,w in records:
            if w:
                assert len(w)==193 and not chords(w)
                assert all(signature(x,axes,phase)==signature(y,axes,phase) for x,y in zip(w,bank[row]))
        print(log.name,dict(stats),'sample independently encoded',dict(checked),flush=True)
if __name__=='__main__':main()
