"""Keep a checkerboard half of the projection; freely choose the other half in both layers."""
import argparse
import gzip
import json
import random
from search_q9_flexible_columns import complete
from search_q9_unordered_projection import project
from verify_q9_center_avoidance import verify

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source');ap.add_argument('count',type=int)
    ap.add_argument('free_states',type=int);ap.add_argument('budget',type=int);ap.add_argument('--retry');ap.add_argument('--min-changes',type=int,default=1);args=ap.parse_args()
    reader=gzip.open if args.source.endswith('.gz') else open
    with reader(args.source,'rt') as f:bank=[list(map(int,s.split())) for s in f]
    ctrl=json.load(open('q9_explicit_q8_96_plus_94.json'))['vertices'];h=project(ctrl,8);S={x%256 for x in h}
    patch={v for v in range(256) if v.bit_count()%2}
    st,w=complete(h,S^set(sorted(patch)[:3]),patch,191,40000,3,S-patch,0)
    assert st=='FOUND';verify(w);print(json.dumps(['control',st,w]),flush=True)
    jobs=[(i,d,c) for i in range(len(bank)) for d in range(9) for c in (0,1)]
    random.Random(84791).shuffle(jobs)
    if args.retry:jobs=[r[:3] for r in map(json.loads,open(args.retry)) if r[0]!='control' and r[3]=='UNKNOWN']
    seen=set()
    for i,d,c in jobs:
        h=project(bank[i],d);s={v%256 for v in h};patch={v for v in range(256) if v.bit_count()%2!=c};frozen=sorted(s-patch)
        rng=random.Random(1000*i+2*d+c);rng.shuffle(frozen)
        frozen=frozenset(frozen[min(args.free_states,len(frozen)):])
        key=(frozenset(s-patch),frozenset(x for x in h if x%256 in frozen),c,frozenset(s&patch) if args.min_changes else None)
        if key in seen:continue
        seen.add(key);st,w=complete(h,s,patch,192,args.budget,args.min_changes,frozen,c)
        print(json.dumps([i,d,c,st,w],separators=(',',':')),flush=True)
        if w or len(seen)>=args.count:break
if __name__=='__main__':main()
