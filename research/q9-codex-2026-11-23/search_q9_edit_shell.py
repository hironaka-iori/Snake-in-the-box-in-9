"""Search exact edit shells with the parity lower bounds from the port batch."""
import argparse
import json
from pathlib import Path
from search_q9_bounded_edits import solve
from verify_q9_center_avoidance import verify

def splits(p,r):
    def order(a,b):return (b,a) if p[0].bit_count()%2 else (a,b)
    for k in range(2,r-2):
        yield 'same',order(k,r-k),order(k,r-k)
    for t in range(2,r-2):
        u=r-1-t
        yield 'flipped',order(u+1,t),order(u,t+1)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('r',type=int);ap.add_argument('budget',type=int);ap.add_argument('--stride',type=int,default=1);a=ap.parse_args()
    bank=Path('q9_port_all_new_plateau.txt').read_text().splitlines()
    for i in range(0,len(bank),a.stride):
        p=list(map(int,bank[i].split()))
        for name,drops,adds in splits(p,a.r):
            st,_,_,w=solve(p,a.r,a.budget,(drops,adds))
            print(json.dumps([i,a.r,name,drops,adds,st,w],separators=(',',':')),flush=True)
            if w:
                verify(w);assert len(w)==193;raise SystemExit
