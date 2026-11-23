from bank import *
from solver import solve
from itertools import combinations
import sys
def part(ds):
    if not ds:yield ();return
    for c in ds[1:]:
        for tail in part([x for x in ds if x not in (ds[0],c)]):yield ((ds[0],c),)+tail
ps=[(g,s) for s in range(9) for g in part([i for i in range(9) if i!=s])]
word=trans(json.loads((r/'q9_explicit_q8_96_plus_94.json').read_text())['vertices'])
prev=[json.loads(line) for line in (d/'knownq8.jsonl').open()]
updates={z['line']:z for z in (json.loads(line) for line in (d/'retry.jsonl').open()) if z['source']=='knownq8'}
old={(z['w'],z['group']) for i,z in enumerate(prev) if z['target']==192 and z['left']==2 and z['right']==2 and updates.get(i,z)['status']=='UNSAT'}
for off in range(int(sys.argv[1]),4,2):
    w=word[off:off+188];count=0;new={}
    for pi,(g,s) in enumerate(ps):
        if (w,pi) in old:count+=1;continue
        st,p,k=solve(list(map(int,w)),g,s,2,2,60000);new[st]=new.get(st,0)+1
        if st!='UNSAT':
            print(json.dumps(dict(offset=off,w=w,group=pi,ps=g,s=s,left=2,right=2,target=192,status=st,conflicts=k,path=p)),flush=True)
            if p:assert valid(p);raise SystemExit
    print(json.dumps(dict(offset=off,reused=count,new=new)),flush=True)
