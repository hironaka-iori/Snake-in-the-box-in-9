from pathlib import Path
from itertools import combinations
from collections import Counter
import sys
from pool_sat import solve,rows
D=Path(__file__).resolve().parent
hosts=list(map(set,rows('q8_all_191_positive.hosts')))
four=[m for m in range(512) if m.bit_count()==4]
six=[m for m in range(512) if m.bit_count()==6]
remaining=set(four);assignment={}
while remaining:
    parent=max(six,key=lambda p:(sum(p&m==m for m in remaining),-p))
    old={m for m in remaining if m&parent==m}
    for m in old:assignment[m]=parent
    remaining-=old
def face(mask,base):return {v for v in range(512) if (v&~mask)==base}
for row,host in enumerate(hosts):
    cases={};res={};counts=Counter()
    for f in four:
        for u in range(512):
            if f&u:continue
            parent=assignment[f];mid=f|((parent^f)&-(parent^f))
            cases[f,u]=(parent,u&~parent),(mid,u&~mid)
    for lev,budget in ((6,450),(5,1400),(4,8000)):
        todo=set()
        for basepair,chain in cases.items():
            if any(res.get(parent)=='UNSAT' for parent in (*chain,basepair)):continue
            todo.add(chain[0] if lev==6 else chain[1] if lev==5 else basepair)
        for mask,anchor in sorted(todo):
            F=face(mask,anchor);status,n,w=solve(host|F,192,budget)
            print(status,row,mask,anchor,'exterior',len(F-host),'rounds',n,*(w or []),flush=True)
            if w:raise SystemExit
            res[mask,anchor]=status;counts[lev,status]+=1
    solved=sum(any(res.get(key)=='UNSAT' for key in (*chain,i)) for i,chain in cases.items())
    print('ROW',row,'four_cases',len(cases),'resolved',solved,'counts',dict(counts),flush=True)
print('DONE',flush=True)

