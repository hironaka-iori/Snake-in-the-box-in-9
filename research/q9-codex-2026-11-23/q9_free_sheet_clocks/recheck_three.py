"""Independent explicit physical vertex occupancy for one freely timed axis and one recolorable pair."""
from collections import defaultdict,Counter
from itertools import combinations
from pathlib import Path
import json,random
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Glucose4
from sheet import valid,ROOT

def check(word,s,pair,target):
    pool=IDPool();clauses=[];cross=[];levels=[];colors=[];fixed=0;par=0;frames=[];steps=[int(a) for a in word if int(a)!=s]
    for i in range(len(steps)+2):levels.append(pool.id())
    lookup=defaultdict(list)
    for i in range(len(steps)+1):
        if i:
            a=steps[i-1]
            if a in pair:par^=1
            else:fixed^=1<<a
        color=pool.id();colors.append(color)
        if i==0:clauses.append([-color])
        elif steps[i-1] not in pair:clauses.extend([[color,-colors[i-1]],[-color,colors[i-1]]])
        a,b=levels[i:i+2];z=pool.id();cross.append(z)
        clauses.extend([[-z,a,b],[-z,-a,-b],[z,-a,b],[z,a,-b]])
        if i:clauses.append([-z,-cross[i-1]])
        opts=[]
        for c in range(2):
            for sheet in range(2):
                h=pool.id();base=fixed | (c<<pair[0]) | ((c^par)<<pair[1]) | (sheet<<s)
                lit=color if c else -color
                l=a if sheet else -a;r=b if sheet else -b
                clauses.extend([[-lit,-l,h],[-lit,-r,h],[-h,lit],[-h,l,r]])
                for v in [base,*[base^(1<<k) for k in range(9)]]:
                    for j,other in lookup[v]:
                        if j<i-1:clauses.append([-h,-other])
                opts.append((base,h))
        for base,h in opts:lookup[base].append((i,h))
        frames.append(opts)
    clauses.append([-levels[0]])
    need=target-len(steps)
    if need>len(cross):return 'UNSAT'
    if need>0:clauses.extend(CardEnc.atleast(cross,bound=need,vpool=pool,encoding=EncType.totalizer).clauses)
    with Glucose4(bootstrap_with=clauses) as sol:
        sol.conf_budget(220000);r=sol.solve_limited()
        if r!=True:return 'UNKNOWN' if r is None else 'UNSAT'
        m=set(sol.get_model())
    out=[]
    for i,opts in enumerate(frames):
        pts=[v for v,h in opts if h in m];pts.sort(key=lambda v:bool(v&(1<<s))!=(levels[i] in m));out.extend(pts)
    assert len(out)>target and valid(out)
    return 'FOUND'
def main():
    d=Path(__file__).parent;p=json.loads((ROOT/'q9_explicit_q8_96_plus_94.json').read_text())['vertices']
    w=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
    r=random.Random(8174)
    def penalty(w):
        vs=[0]
        for t in w:vs.append(vs[-1]^(1<<int(t)))
        return sum((a^b).bit_count()<2 for i,a in enumerate(vs) for b in vs[:max(0,i-1)])
    candidates=[v for v in (ROOT/'q9_via_q10/monotone_near.words').read_text().split() if len(v)==192 and penalty(v)==2]
    for i in range(8):
        ds=list(range(9));r.shuffle(ds)
        st=check(w,ds[0],ds[1:3],191);print(json.dumps(dict(control=i,status=st)),flush=True)
    for name,seeds in [('free3_explicit',[w]),('free3_near',candidates)]:
        rows=[json.loads(l) for l in (d/(name+'.jsonl')).read_text().splitlines()];r.shuffle(rows)
        for row in rows:
            st=check(seeds[row['seed']],row['sheet'],row['flex'],192)
            print(json.dumps(dict(dataset=name,seed=row['seed'],sheet=row['sheet'],flex=row['flex'],status=st)),flush=True)
            if st!='UNKNOWN':assert st==row['status']
if __name__=='__main__':main()
