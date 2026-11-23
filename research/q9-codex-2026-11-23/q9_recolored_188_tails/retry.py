from bank import *
from solver import solve
import sys
for f in sys.argv[1:] or ['public','knownq8','q8','onechordmixed','onechordfull']:
    for i,line in enumerate((d/(f+'.jsonl')).open()):
        z=json.loads(line)
        if z['status']!='UNKNOWN':continue
        st,p,c=solve(list(map(int,z['w'])),z['ps'],z['s'],z['left'],z['right'],200000)
        print(json.dumps(dict(source=f,line=i,status=st,path=p,conflicts=c)),flush=True)
        if p:
            assert len(p)==z['target']+1 and valid(p)
            raise SystemExit
