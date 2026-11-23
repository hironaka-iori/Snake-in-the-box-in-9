import json
from pathlib import Path
from itertools import groupby
from collections import Counter
root=Path(__file__).resolve().parent
names=['trial','half','eight','gen2','repair','warm']
summary={};best=[];bestOrder=None;bank={}
for k in names:
    lines=(root/(k+'.log')).read_text().splitlines()
    runs=[l for l in lines if l.startswith('RUN ')]
    checked=0;classes=set()
    for l in lines:
        vals=l.split()
        if vals[0]!='BEST':continue
        _,n,w,r,it,*v=vals;p=list(map(int,v)); n=int(n)
        chunks=[list(a) for _,a in groupby(p,key=lambda x:x//32)]
        assert len(chunks)==16 and len(set(p))==n+1==len(p)
        order=[c[0]//32 for c in chunks]
        w2=''.join(str((v^t).bit_length()-1) for v,t in zip(order,order[1:]))
        assert w2==w
        assert all(((x^y).bit_count()==1)==(j==i+1) for j,y in enumerate(p) for i,x in enumerate(p[:j]))
        checked+=1;classes.add(w)
        if len(p)>len(best):best=p;bestOrder=w
        if n>=180:
            fields=[]
            for c in chunks:fields.extend((sum(1<<(x%32) for x in c),c[0]%32))
            fields.append(p[-1]%32)
            bank[(w,tuple(fields))]='STATE '+w+' 0 '+str(n+1)+' '+' '.join(map(str,fields))
    summary[k]=dict(runs=len(runs),last=runs[-1] if runs else '',witness_rows_validated=checked,distinct_orders_in_logged_witnesses=len(classes))
(root/'validstates.txt').write_text('\n'.join(bank.values())+'\n')
(root/'best.json').write_text(json.dumps(dict(edges=len(best)-1,vertices=len(best),pairs=len(best)*(len(best)-1)//2,order=bestOrder,path=best),indent=2)+'\n')
(root/'trials.json').write_text(json.dumps(summary,indent=2)+'\n')
