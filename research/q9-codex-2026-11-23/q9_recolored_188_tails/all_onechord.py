from bank import *
from solver import solve
import sys
def canon(w):
    def k(t):
        m={};return tuple(m.setdefault(x,len(m)) for x in t)
    return min(k(w),k(w[::-1]))
def parts(ds):
    if not ds:yield ();return
    a=ds[0]
    for b in ds[1:]:
        for rest in parts([x for x in ds if x not in (a,b)]):yield ((a,b),)+rest
partitions=[(ps,s) for s in range(9) for ps in parts([x for x in range(9) if x!=s])]
ws=[trans(list(map(int,l.split()))) for l in (r/'q8_complete_single_cross_near_192.txt').read_text().splitlines()]
orbits={canon(ws[0][2:190]):(0,2)}
for i,w in enumerate(ws):
    for off in range(5):orbits.setdefault(canon(w[off:off+188]),(i,off))
job,reps=map(int,sys.argv[1:]);assigned=list(orbits.values())[1:][job::reps]
for i,off in assigned:
    w=ws[i][off:off+188];counts={}
    for pi,(ps,s) in enumerate(partitions):
        st,p,k=solve(list(map(int,w)),ps,s,2,2,30000)
        counts[st]=counts.get(st,0)+1
        if st!='UNSAT':
            print(json.dumps(dict(idx=i,offset=off,w=w,group=pi,ps=ps,s=s,left=2,right=2,target=192,status=st,conflicts=k,**({'path':p} if p else {}))),flush=True)
            if p:assert valid(p) and len(p)==193;sys.exit()
    print(json.dumps(dict(idx=i,offset=off,counts=counts)),flush=True)
