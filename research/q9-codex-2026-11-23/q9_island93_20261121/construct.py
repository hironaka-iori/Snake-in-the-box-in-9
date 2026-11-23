from geom import *
import subprocess
from collections import Counter
sel,rows=regs()
raw={}
for r in rows:
    k=r['i'],r['c']
    if k not in raw or r['score']<raw[k]['score']:raw[k]=r
rank=sorted([i for i in {q['i'] for q in rows} if any((i,c) not in sel for c in range(4)) and i not in (962,1215)],key=lambda i:(-max(raw[i,c]['best_previous'] for c in range(4)),-max(raw[i,c]['score'] for c in range(4) if (i,c) not in sel),i))[:32]
(D/'construction_ids.json').write_text(json.dumps(rank)+'\n')
with (D/'mixed.paths').open('w') as out,(D/'mixed.log').open('w') as log:
    with __import__('tempfile').TemporaryDirectory() as tmp:
        p=Path(tmp)/'result'
        for i in rank:
            ans=subprocess.check_output([old/'tail',old/'regrown_upper.words',old/'cases.dat',p,'60','1',str(i),str(i+1)],text=True)
            print(i,ans.strip(),file=log,flush=True)
            for ln in p.read_text().splitlines():
                loc,n,*v=map(int,ln.split());assert loc==i and n+1==len(v)==len(set(v))
                assert all(((x^y).bit_count()==1)==(a==b+1) for a,x in enumerate(v) for b,y in enumerate(v[:a]))
                L=set(cases[i]['lo']+cases[i]['edge']);assert {x for x in v if x<256}==L and sum((x^y)==256 for x,y in zip(v,v[1:]))==3
                print(ln,file=out,flush=True)
                if n>=192:raise SystemExit
