from iso_solve import load,family
from sat import solve
from build import D
import json
for typ in ('target','rest'):
    ss,fs=load(typ)
    for line in (D/('iso_'+typ+'.jsonl')).read_text().splitlines():
        r=json.loads(line)
        if r['status']!='LIMIT':continue
        src,m,col=r['src'],r['mode'],r['majority']
        raw,pool,hard,picks=family(ss,fs,src,m)
        assert picks==r['picks'] and len(pool)==r['union'] and len(hard)==r['hard']
        ans=solve(pool,hard,raw,193,80000,col);ans.update(src=src,mode=m,majority=col,typ=typ)
        print(json.dumps(ans),flush=True)
        if ans['path']:break
