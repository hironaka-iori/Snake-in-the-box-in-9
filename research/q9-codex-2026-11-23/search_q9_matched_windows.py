"""Recombine short donor walks mapped isometrically onto two fixed ports."""
import argparse
import json
import random
from collections import defaultdict
from pathlib import Path
from search_q9_time_vertex_lists import check,solve_domains

def mapped_segment(q,s,lo,hi,rng):
    u=q[0]^q[-1];v=s[lo]^s[hi]
    axis=[None]*9
    for side in (0,1):
        left=[j for j in range(9) if (u>>j)&1==side]
        right=[j for j in range(9) if (v>>j)&1==side]
        if len(left)!=len(right):raise ValueError('port distance')
        rng.shuffle(right)
        for a,b in zip(left,right):axis[a]=b
    lookup={0:0}
    out=[s[lo]]
    for x,y in zip(q,q[1:]):
        d=(x^y).bit_length()-1
        out.append(out[-1]^(1<<axis[d]))
    assert out[-1]==s[hi]
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('seeds');ap.add_argument('count',type=int)
    args=ap.parse_args();rng=random.Random(862913)
    donors=[list(map(int,l.split())) for l in Path('/private/tmp/q9_191_published_bank20.pts').read_text().splitlines()]
    seeds=[list(map(int,l.split())) for l in Path(args.seeds).read_text().splitlines()]
    bins=defaultdict(list)
    lengths=(4,6,8,12,16,20,28,40,56)
    for k,p in enumerate(donors):
        for n in lengths:
            for lo in range(0,len(p)-n,2):
                bins[n,(p[lo]^p[lo+n]).bit_count()].append((k,lo))
    ctrl=json.loads(Path('q9_independent_connectors_damaged_control.json').read_text())['source']
    donor=json.loads(Path('q9_time_vertex_lists_first.jsonl').open().readline())[3]
    for i in range(-1,args.count):
        if i<0:index=-1;s=ctrl
        else:index=rng.randrange(len(seeds));s=seeds[index]
        bad=[(a,b) for b,y in enumerate(s) for a,x in enumerate(s[:b-1]) if (x^y).bit_count()<=1]
        focus=sorted(set(x for pair in bad for x in pair))
        assert focus
        domains=[{x} for x in s]
        if i<0:
            # Supply an admissible donor subwalk undoing a known defect.
            for t in range(min(focus)-1,max(focus)+2):domains[t].add(donor[t])
        for trial in range(60):
            n=rng.choice(lengths);t=rng.choice(focus) if trial%4 else rng.randrange(len(s))
            lo=max(0,min(len(s)-n-1,t-rng.randrange(1,n)));hi=lo+n
            candidates=bins[n,(s[lo]^s[hi]).bit_count()]
            if not candidates:continue
            fixed=set(s[:lo]+s[hi+1:]);neighbors={v^(1<<d) for v in fixed for d in range(9)}
            best=None
            for attempt in range(40):
                k,left=rng.choice(candidates);q=donors[k][left:left+n+1]
                if rng.randrange(2):q=q[::-1]
                z=mapped_segment(q,s,lo,hi,rng)
                if z==s[lo:hi+1]:continue
                penalty=sum(4*(v in fixed)+(v in neighbors) for v in z[1:-1])
                if best is None or penalty<best[0]:best=penalty,z
                if not penalty:break
            if best:
                for j,v in enumerate(best[1],lo):domains[j].add(v)
        status,w=solve_domains(s,domains,10000)
        print(json.dumps([i,index,len(bad),sum(map(len,domains)),status,w]),flush=True)
        if i<0:assert status=='FOUND' and len(w)==192 and check(w)
        elif w:
            assert check(w) and len(w)==193
            break
if __name__=='__main__':main()
