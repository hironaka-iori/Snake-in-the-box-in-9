from common import *
from runs import sizes
import json
with (D/'retry.jsonl').open('w') as out:
    for f in [*sorted(D.glob('target*.jsonl')),*sorted(D.glob('cross*.jsonl'))]:
        for i,l in enumerate(f.read_text().splitlines()):
            s=json.loads(l)
            if s['status']!='UNKNOWN':continue
            w=list(map(int,s['w']));p=s['pairs'];lens=sizes(len(w),s['spans']);st,path,c=solver.solve(w,p,s['single'],lens,250000)
            row=dict(file=f.name,row=i,status=st,conflicts=c)
            if path:check(w,p,s['single'],lens,path);row['path']=path
            print(json.dumps(row),file=out,flush=True)
