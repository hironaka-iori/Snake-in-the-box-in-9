"""Retry inconclusive archived search inputs at higher node budget."""
import argparse,gzip,json,os,subprocess
from pathlib import Path
from audit import HERE,valid,fixed_cases,rows
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--budget',type=int,default=140000);ap.add_argument('--seconds',type=int,default=90);a=ap.parse_args()
    for r in rows(HERE/'branch12.jsonl'):
        if r['status']!='UNKNOWN':continue
        r=dict(r);payload=gzip.open(HERE/r['input'],'rb').read()
        env={**os.environ,'Q9_PATH_MINIMUM':'1'};env.pop('Q9_AVOID_SHAPES',None)
        try:
            out=subprocess.run([str(HERE/'factor'),str(a.budget)],input=payload,stdout=subprocess.PIPE,env=env,check=True,timeout=a.seconds).stdout.decode().split()
        except subprocess.TimeoutExpired:
            r['status']='TIMEOUT';r['seconds']=a.seconds;print(json.dumps(r),flush=True);continue
        idx,st,nn,*path=out;assert int(idx)==r['row'];r.update(status=st,nodes=int(nn),cap=a.budget)
        if path:
            w=list(map(int,path));h=r['signature'];f=next(f for _,i,f in fixed_cases(12) if i==r['row'])
            assert valid(w) and f<=set(w) and len(w)>=r['goal']+1 and (len(w)-r['goal']-1)%2==0 and (h==2 or w[0].bit_count()%2==h)
            r['witness']=w
        print(json.dumps(r),flush=True)
if __name__=='__main__':main()
