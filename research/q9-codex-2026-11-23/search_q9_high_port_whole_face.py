"""Search a free Q8 partner using two endpoint colours, without prescribing individual crossings."""
import argparse
from collections import defaultdict
import gzip
import json
import os
from pathlib import Path
import time

from search_q9_shell_dual import solve
from verify_q9_intact98_all_crossings import check
from verify_q9_high_port_completions import allowed

def verify(p,low,goal,ep):
    check(len(p)==goal+1==len(set(p)) and {v for v in p if v<256}==low,'wrong fixed facet')
    check(all(((v^w).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j,w in enumerate(p) if j>i),'invalid witness')
    check(goal%2 or p[0].bit_count()%2==ep,'end colour mismatch')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('bank');ap.add_argument('binary');ap.add_argument('--time',type=float,default=100);ap.add_argument('--budget',type=int,default=12000)
    ap.add_argument('--certs',type=Path,required=True);a=ap.parse_args()
    a.certs.mkdir(exist_ok=True)
    os.environ.update(Q9_SHELL_SOLVER=a.binary,Q9_SHELL_CERT_DIR=str(a.certs),Q9_SHELL_PARTS='8')
    os.environ.pop('Q9_PATH_MINIMUM',None);os.environ.pop('Q9_AVOID_SHAPES',None)
    data=[[json.loads(l) for l in open(f)] for f in ('q9_port_highdim_free_face.jsonl','q9_port_highdim_exact192.jsonl')]
    ids={r[0] for r in data[0][1:] if r[-2]=='UNKNOWN'}&{r[0] for r in data[1][1:] if r[-2]=='UNKNOWN'}
    raw=Path(a.bank).read_text().splitlines()
    prev=defaultdict(dict)
    for fn in ('q9_high_port_free_layer_trials.jsonl','q9_high_port_free_layer_narrow.jsonl','q9_high_port_free_layer_retry.jsonl'):
        for r in map(json.loads,open(fn)):
            if r['index']!='control':prev[r['index']][tuple(r['ports']),tuple(r['full'])]=r
    jobs=[]
    for i in ids:
        low=set(map(int,raw[i].split()[1:]));req=set(allowed(low))
        done={k for k,r in prev[i].items() if r['status'] in ('DUAL','EXHAUSTED','EMPTY')}
        if req<=done:continue
        if req-done:
            for h in sorted({0 if full[0]==2 else 1 for po,full in req-done}):
                # Test positive candidates where fixing all tips produced the largest upper estimates.
                upper=max((r.get('upper',0) for r in prev[i].values()),default=0)
                jobs.append((-upper,i,h,low))
    def go(i,h,low,goal,nodes,anchors=()):
        upper={v+256 for v in range(256) if v not in low or sum(v^(1<<d) in low for d in range(8))<=1}
        _,_,_,_,status,numerator,p=solve((i,sorted(low),0,h,goal,nodes,low|set(anchors),low|upper))
        if p:verify(p,low,goal,h)
        print(json.dumps(dict(index=i,goal=goal,ep=h,upper_control_anchors=len(anchors),status=status,integer_vertex_numerator=numerator,witness=p),separators=(',',':')),flush=True)
        return status
    p=data[0][0][-1];low={v for v in p if v<256};start=time.monotonic()
    if go(-2,0,low,len(p)-1,30000,[v for v in p if v>=256][::3])!='FOUND':raise SystemExit('positive control failed')
    for _,i,h,low in sorted(jobs,key=lambda t:t[:3]):
        if time.monotonic()-start>=a.time:break
        if go(i,h,low,192,a.budget)=='FOUND':break
if __name__=='__main__':main()
