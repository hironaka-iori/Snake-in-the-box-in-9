"""Seek a common reduced anchor set whose two endpoint colours both have integer certificates."""
import json, os, random
from pathlib import Path
from relax import assess, value, simplify
def main():
    root=Path(__file__).parent
    dest=root/'shared_duals';dest.mkdir(exist_ok=True)
    cs=[json.loads((root/'relaxed_duals'/f'rem69_e{e}.json').read_text()) for e in (0,1)]
    original=set(json.loads((root/'relaxed_duals'/'full75_e0_n16.json').read_text())['fixed'])
    sets=[set(c['fixed']) for c in cs]
    accepted=None
    for F in [sets[0]&sets[1],sets[0],sets[1],original]:
        both=[]
        for e in (0,1):
            r,c=assess(F,set(),e,22,f'start{len(F)}_{sum(F)}_e{e}',dest)
            print(json.dumps(r),flush=True)
            if r['status']!='DUAL_EXCLUSION':break
            both.append(c)
        if len(both)==2:
            accepted=(F,both);break
    assert accepted
    F,cs=accepted;randomizer=random.Random(732)
    for iteration in range(30):
        scored=[]
        for v in F:
            after=[simplify(F-{v},set(),192,e) for e in (0,1)]
            scored.append((sum(len(A) for _,A,_ in after),-sum(len(P) for P,_,_ in after),randomizer.random(),v,after))
        rank=[]
        for _,_,_,v,domains in sorted(scored)[:16]:
            t=[value(c,P,A,192,e) for e,((P,A,_),c) in enumerate(zip(domains,cs))]
            rank.append((max(t),sum(t),v,t))
        bound,_,winner,values=min(rank);guess=F-{winner}
        if bound>=1930000:
            new=[]
            for e in (0,1):
                r,c=assess(guess,set(),e,24,f'refit{len(guess)}_{sum(guess)}_e{e}',dest)
                print(json.dumps(r),flush=True)
                if r['status']!='DUAL_EXCLUSION':break
                new.append(c)
            if len(new)<2:break
            cs=new
        else:
            cs=[{**c,'index':f'shared{len(guess)}_{sum(guess)}_e{e}','fixed':sorted(guess),'upper':n} for e,(n,c) in enumerate(zip(values,cs))]
            for c in cs:
                (dest/(c['index']+'.json')).write_text(json.dumps(c,separators=(',',':'))+'\n')
                print(json.dumps({k:c[k] for k in ('index','upper','ep','fixed','excluded')}),flush=True)
        F=guess
if __name__=='__main__':main()
