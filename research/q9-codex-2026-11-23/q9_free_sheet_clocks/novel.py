from sheet import ROOT,canonical,solve,valid
from random import Random
from collections import Counter
import sys,json
def main():
    rng=Random(715919);bank=[list(map(int,w)) for w in (ROOT/'q9_gap_generations/prior191.words').read_text().split()];known={canonical(w) for w in bank}
    ctrl=sys.argv[1]=='control';source190=[list(map(int,w)) for w in (ROOT/'q9_gap_generations/prior190.words').read_text().split()]
    for t in range(10 if ctrl else 1400):
        w=rng.choice(bank if ctrl or t%4 else source190);ds=list(range(9));rng.shuffle(ds);s=ds.pop();g=list(zip(ds[::2],ds[1::2]))
        blocked=known-{canonical(w)} if ctrl else known
        st,p=solve(w,g,s,191,50000 if ctrl else 10000,blocked)
        if p:
            word=[(a^b).bit_length()-1 for a,b in zip(p,p[1:])];assert canonical(word) not in blocked and valid(p)
            for side in (p,p[::-1]):
                for d in range(9):
                    q=side+[side[-1]^1<<d]
                    if valid(q):p=q;break
                if len(p)>=193:break
        print(json.dumps(dict(trial=t,status=st,sheet=s,pairs=g,source=''.join(map(str,w)),edges=len(p)-1 if p else None,path=p),separators=(',',':')),flush=True)
        if p and not ctrl:break
if __name__=='__main__':main()
