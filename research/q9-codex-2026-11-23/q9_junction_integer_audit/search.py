import argparse
from collections import deque
from pathlib import Path
import json,os,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from search_q9_shell_dual import solve
from verify_q9_junction_tree import main as check_queue
NB=[{v^(1<<i) for i in range(9)} for v in range(512)]
PAR=[{v for v in range(512) if v.bit_count()%2==h} for h in range(2)]
def load(f):return [json.loads(l) for l in (ROOT/f).read_text().splitlines()]
def extract():
    check_queue()
    Q=deque((set(r['fixed']),set(r['excluded'])) for r in load('q9_junction_second_omission.jsonl') if r['status']=='UNKNOWN')
    for r in load('q9_junction_branch.jsonl'):
        f,e=Q.popleft()
        if r['status']=='UNKNOWN':
            v=r['split'];Q.extend([(f|{v},e),(f,e|{v})])
    return list(Q)
def simplify(F,X,goal,ep):
    F=set(F);A=set(range(512))-X
    while True:
        before=(len(F),len(A));why=None
        fc={v:len(F&NB[v]) for v in A};ac={v:len(A&NB[v]) for v in A}
        if F-A or any(fc[v]>2 for v in F):return F,A,'required degree'
        forced_end={v for v in F if ac[v]==1}
        if len(forced_end)>2 or forced_end-PAR[ep]:return F,A,'endpoint count'
        for h in range(2):
            n=goal//2+int(h==ep)
            if len(PAR[h]&A)<n or len(PAR[h]&F)>n:return F,A,'colour count'
            if len(PAR[h]&F)==n:A-=PAR[h]-F
            if len(PAR[h]&A)==n:F|=PAR[h]&A
        if (len(F),len(A))!=before:continue
        sat={v for v in F if fc[v]==2}
        unseen=set(F);component={}
        while unseen:
            queue=[unseen.pop()]
            for v in queue:
                fresh=NB[v]&unseen;unseen-=fresh;queue.extend(fresh)
            if sum(fc[v] for v in queue)!=2*(len(queue)-1):return F,A,'fixed cycle'
            for v in queue:component[v]=queue[0]
        for v in list(A):
            minimum=2 if v not in PAR[ep] or (len(forced_end)==2 and v not in forced_end) else 1
            if v in F:
                if ac[v]<minimum:return F,A,'forced vertex lacks neighbors'
                if ac[v]==minimum:F|=A&NB[v]
            else:
                if fc[v]>2 or ac[v]<minimum or NB[v]&sat:A.discard(v)
                elif fc[v]==2:
                    a,b=tuple(NB[v]&set(component))
                    if component[a]==component[b]:A.discard(v)
        if (len(F),len(A))==before:return F,A,None

def main():
    p=argparse.ArgumentParser();p.add_argument('binary');p.add_argument('--seconds',type=int,default=240);p.add_argument('--cap',type=int,default=70000);p.add_argument('--parts',type=int,default=12);p.add_argument('--out',default='leaf')
    o=p.parse_args();dest=Path(__file__).parent;certdir=dest/(o.out+'_duals');certdir.mkdir(exist_ok=True)
    os.environ.update(Q9_SHELL_SOLVER=o.binary,Q9_SHELL_CERT_DIR=str(certdir),Q9_SHELL_PARTS=str(o.parts))
    os.environ.pop('Q9_PATH_MINIMUM',None);os.environ.pop('Q9_AVOID_SHAPES',None)
    q=extract();outer=load('q9_junction_first_omission.jsonl');inner=load('q9_junction_second_omission.jsonl')
    f0=set(outer[0]['fixed'])
    jobs=[(i,f,e) for i,(f,e) in enumerate(q)]
    # Strongly constrained leaves first, then their common parent, then broader masks.
    jobs.sort(key=lambda r:len(simplify(r[1],r[2],192,0)[1]))
    commonF=set.intersection(*(f for i,f,e in jobs)); commonX=set.intersection(*(e for i,f,e in jobs))
    extra=[(-2,commonF,commonX),(-3,f0,set()),(-4,f0-{min(f0)},set())]
    jobs=[extra[0]]+jobs+extra[1:]
    path=load('q9_junction_portfolio_positive.json')[0]['vertices'] if False else json.loads((ROOT/'q9_junction_portfolio_positive.json').read_text())['vertices']
    ctrl=set(path);ep=path[0].bit_count()%2
    jobs=[(-1,ctrl,set())]+jobs;start=time.monotonic()
    for i,F,X in jobs:
        if time.monotonic()-start>=o.seconds:break
        g,c=(len(path)-1,ep) if i==-1 else (192,0)
        req,domain,why=simplify(F,X,g,c)
        result=dict(index=i,goal=g,ep=c,pinned=sorted(F),excluded=sorted(X),forced=len(req),domain=len(domain))
        if why:result.update(status='GEOMETRY',reason=why)
        else:
            _,_,_,_,st,num,w=solve((i,sorted(F),0,c,g,o.cap,req,domain))
            result.update(status=st,numerator=num,witness=w)
            if w:assert len(w)==g+1 and len(set(w))==len(w) and F<=set(w) and not set(w)&X and w[0].bit_count()%2==c
        print(json.dumps(result,separators=(',',':')),flush=True)
        if i==-1:assert result['status']=='FOUND'
        elif result['status']=='FOUND':break
if __name__=='__main__':main()
