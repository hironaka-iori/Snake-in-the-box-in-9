"""Explore adding one Q8 column to observed 191 projections, with both layers free."""
import argparse
import gzip
import json
import random
from collections import Counter
from search_q9_unordered_projection import project, solve

def main():
    ap=argparse.ArgumentParser();ap.add_argument('count',type=int);ap.add_argument('budget',type=int);ap.add_argument('seed',type=int);ap.add_argument('--remove',action='store_true');args=ap.parse_args()
    rng=random.Random(args.seed)
    bank=[list(map(int,s.split())) for s in gzip.open('q9_port_followup_public191.txt.gz','rt')]
    candidates=[];used=set()
    for i,p in enumerate(bank):
        for axis in range(9):
            h=project(p,axis);s=frozenset(x%256 for x in h)
            if s in used:continue
            used.add(s);candidates.append((i,axis,h,s))
    rng.shuffle(candidates)
    totals=Counter()
    for i,axis,h,s in candidates[:args.count]:
        neighbors=sorted({v^(1<<k) for v in s for k in range(8)}-s)
        if args.remove:neighbors=sorted(s)
        states=Counter()
        for y in neighbors:
            hint=(h-{y,y+256}) if args.remove else (h|{y})
            st,w=solve(hint,192,args.budget,True)
            states[st]+=1;totals[st]+=1
            if w:
                print(json.dumps(['FOUND',i,axis,y,w]),flush=True);return
            if st=='UNKNOWN':print(json.dumps(['UNKNOWN',i,axis,y]),flush=True)
        print(json.dumps(['SET',i,axis,states]),flush=True)
    print(json.dumps(['DONE',totals]),flush=True)
if __name__=='__main__':main()
