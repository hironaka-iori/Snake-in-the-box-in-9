"""Check coverage using sorted coordinate columns of the retained ordered vertices."""
import argparse
from collections import Counter
import json
from pathlib import Path
from verify_q9_onechord_bank import check


def columns(p):
    return [sum((v>>axis&1)<<i for i,v in enumerate(p)) for axis in range(9)]


def fixed_key(cols,n,start,k):
    # Delete the interval from nine bit columns of the ordered vertex list,
    # then translate its first row to zero and sort by coordinate.
    def direction(c,s):
        mask=(1<<s)-1;full=(1<<(n-k))-1
        trimmed=[(word&mask)|((word>>(s+k))<<s) for word in c]
        return s,tuple(sorted((v^full) if v&1 else v for v in trimmed))
    return min(direction(cols[0],start),direction(cols[1],n-k-start))


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('bank',type=Path);ap.add_argument('k',type=int);ap.add_argument('logs',nargs='+',type=Path);ns=ap.parse_args()
    rows=[list(map(int,l.split())) for l in ns.bank.read_text().splitlines()]
    cols=[(columns(p),columns(p[::-1])) for p in rows]
    multiplicities=Counter()
    for i,p in enumerate(rows):
        a,b=check(p)
        starts=set.union(*(set(range(max(0,j-ns.k+1),min(j,len(p)-ns.k)+1)) for j in (a,b)))
        for start in starts:multiplicities[fixed_key(cols[i],len(p),start,ns.k)]+=1
    state={}
    for log in ns.logs:
        for l in log.read_text().splitlines():
            r=json.loads(l);row=r['row'];assert r['k']==ns.k
            key=fixed_key(cols[row],len(rows[row]),r['start'],ns.k);assert key in multiplicities
            if key in state:assert state[key]=='UNKNOWN' or r['status'] in (state[key],'UNKNOWN')
            if r['status']!='UNKNOWN' or key not in state:state[key]=r['status']
            if r['witness']:
                from verify_q9_six_cube_coverage import pairwise
                pairwise(r['witness'],len(r['witness'])-1);assert len(r['witness'])>=193
    counts=Counter();unique=Counter()
    for key,num in multiplicities.items():
        st=state.get(key,'pending');counts[st]+=num;unique[st]+=1
    print(json.dumps(dict(walks=len(rows),span=ns.k,total_windows=sum(counts.values()),windows=counts,distinct_domains=len(multiplicities),domains=unique)))
