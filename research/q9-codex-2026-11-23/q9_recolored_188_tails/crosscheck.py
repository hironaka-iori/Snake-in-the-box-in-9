from bank import *
import sys
sys.path.append(str(r/'q9_pair_clocks'))
from domains import solve
rng=random.Random(781)
for source in ['onechordfull','q8','public']:
    rows=[json.loads(l) for l in (d/(source+'.jsonl')).open()]
    for i in rng.sample([k for k,z in enumerate(rows) if z['status']=='UNSAT'],4):
        z=rows[i];w=list(map(int,z['w']));a=z['left'];b=z['right'];lookup={x:pair for pair in z['ps'] for x in pair};lookup[z['s']]=[z['s']]
        domains=[set(range(9))]*a+[set(lookup[c]) for c in w]+[set(range(9))]*b
        st,p,k=solve([0]*a+w+[0]*b,domains,15000)
        assert st!='FOUND'
        print(json.dumps(dict(source=source,line=i,other_status=st,conflicts=k)),flush=True)
