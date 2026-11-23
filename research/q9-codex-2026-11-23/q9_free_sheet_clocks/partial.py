from itertools import combinations
from random import Random
from sheet import solve,ROOT
import json,sys
def run():
    mode=sys.argv[1];r=Random(910715)
    if mode=='explicit':
        p=json.loads((ROOT/'q9_explicit_q8_96_plus_94.json').read_text())['vertices']
        seeds=[''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))]
    else:
        seeds=[w for w in (ROOT/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==192]
        def penalty(w):
            p=[0]
            for d in map(int,w):p.append(p[-1]^(1<<d))
            return sum((x^y).bit_count()<2 for j,x in enumerate(p) for y in p[:max(0,j-1)])
        seeds=[w for w in seeds if penalty(w)==2]
    jobs=[(k,s,p) for k in range(len(seeds)) for s in range(9) for p in combinations([a for a in range(9) if a!=s],2)]
    r.shuffle(jobs)
    for k,s,p in jobs:
        d=[a for a in range(9) if a!=s and a not in p];g=[p,*zip(d[::2],d[1::2])]
        st,v=solve(list(map(int,seeds[k])),g,s,192,40000,fixed=(1,2,3))
        print(json.dumps(dict(seed=k,sheet=s,flex=p,status=st,path=v)),flush=True)
        if v:break
if __name__=='__main__':run()
