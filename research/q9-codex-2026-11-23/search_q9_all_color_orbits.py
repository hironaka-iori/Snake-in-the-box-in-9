"""Try every nonzero even XOR direction for every 191-edge parent."""
import argparse
import gzip
import json
from q9_pair_selector import search
from verify_q9_center_avoidance import forms, verify


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("start",type=int);ap.add_argument("stop",type=int)
    ap.add_argument("--budget",type=int,default=5500)
    ap.add_argument("--retry",help="read only unresolved instances from an earlier run")
    opt=ap.parse_args()
    paths={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192:
            key=forms(p,191)[0]
            if key not in paths:verify(p);paths[key]=p
    masks=[t for t in range(1,512) if not t.bit_count()%2]
    pending=None
    if opt.retry:
        pending={(i,s,t) for i,s,t,k,st,w in map(json.loads,open(opt.retry)) if st=="UNKNOWN"}
    for i,p in enumerate(paths.values()):
        if not opt.start<=i<opt.stop:continue
        for s in (0,1):
            side=set(p[s::2])
            for t in masks:
                if pending is not None and (i,s,t) not in pending:continue
                pairs=[(v,v^t) for v in sorted(side) if (v^t) not in side]
                st,w=search(side,pairs,t,set(p),192,opt.budget)
                if w:
                    verify(w);assert len(w)==193
                    m=set(w[1::2])
                    assert all((v in m)+(v^t in m)==(v in side)+(v^t in side) for v in range(512))
                print(json.dumps([i,s,t,len(pairs),st,w],separators=(",",":")),flush=True)
                if w:return


if __name__=="__main__":main()
