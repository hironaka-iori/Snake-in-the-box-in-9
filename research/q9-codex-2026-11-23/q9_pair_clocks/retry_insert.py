from incremental import solve
from search import D,partition,validate
import sys,json,random
from collections import Counter
file,mode,seed=sys.argv[1:]
rng=random.Random(int(seed));p=json.loads((D.parent/'q9_explicit_q8_96_plus_94.json').read_text())['vertices'];w=[(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
donors=[list(map(int,x)) for x in (D.parent/'q9_gap_generations/prior191.words').read_text().split()]
parts=[(ps,s) for s in range(9) for ps in partition(tuple(d for d in range(9) if d!=s))]
rows=[d for line in (D/file).read_text().splitlines() if (d:=json.loads(line)).get('status')=='UNKNOWN'];rng.shuffle(rows);stats=Counter()
for row in rows:
    if mode=='single':idx=row['partition'];ps,s=parts[idx];e=row['group'];word=w
    else:idx=row['partition'];ps,s=parts[idx];e=row['extra'];word=donors[row['row']]
    st,v,h,c=solve(word,ps,s,e,75000);stats[st]+=1
    if v:assert len(v)==193 and validate(v)
    print(json.dumps(dict(row=row.get('row'),partition=idx,extra=e,status=st,conflicts=c,**({'found':v,'seam':h} if v else {}))),flush=True)
    if v:break
print(json.dumps(dict(done=True,counts=stats,initial=len(rows))),flush=True)
