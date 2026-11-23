from pathlib import Path
import json,gzip,sys
from collections import Counter
D=Path(__file__).resolve().parent;R=D.parent;inc=R/'q9_group_walk'
prefix=sys.argv[1] if len(sys.argv)>1 else "";seen={};stats={}; C=Counter()
for fn in ['rotate191','rotate189']:
    n=0
    for l in (inc/(fn+'.log')).read_text().splitlines():
        if not l.startswith('BANK '):continue
        a=list(map(int,l.split()[1:]))
        if len(a)!=197:continue
        p=tuple(a[4:]);assert len(p)==193 and all(0<=v<512 for v in p);n+=1
        if p not in seen:
            bad=sum((x^y).bit_count()<=1 for i,x in enumerate(p) for y in p[:max(0,i-1)])+sum((x^y).bit_count()!=1 for x,y in zip(p,p[1:]));seen[p]=(fn,a[0],bad);C[bad]+=1
    stats[fn]=n
keys=sorted(seen,key=lambda p:seen[p][2]);keys=[p for p in keys if not prefix or seen[p][2]==1]
(D/(prefix+'bank.txt')).write_text(''.join(' '.join(map(str,p))+'\n' for p in keys))
(D/(prefix+'source.json')).write_text(json.dumps(dict(source_rows=stats,unique=len(keys),raw_conflict_hist=C,index=[seen[k] for k in keys]),indent=2)+'\n')
(D/'positive.txt').write_text(''.join(gzip.open(R/'q9_port_followup_public191.txt.gz','rt').readlines()[:24]))
print(stats,len(keys),min(C),max(C))
