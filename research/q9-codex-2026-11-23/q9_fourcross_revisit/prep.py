from pathlib import Path
D=Path(__file__).resolve().parent;P=D.parent/'q9_fourcross_new94'
from itertools import groupby
import json
def get(src,row,bank,fs):
    raw=list(map(int,(P/'seeds.dat').read_text().splitlines()[src].split()));original=raw[2:2+raw[1]];seed,rev,lo,hi,n,*z=map(int,(P/bank).read_text().splitlines()[row].split());old=original[::-1] if rev else original;short=z[n+1:];hint=[list(map(int,t.split()))[5:] for t in (P/fs).read_text().splitlines() if int(t.split()[1])==row][-1];return dict(source=src,row=row,anchor=old[lo:hi+1],short=short,hint=hint,L=n-1)
rows=[get(1,1,'freer92.dat','free184.paths'),get(0,1,'spliced.dat','linked0.paths')]
(D/'cases.json').write_text(json.dumps(rows))
with (D/'inputs.dat').open('w') as out:
    for r in rows:print(r['source'],len(r['anchor']),*r['anchor'],len(r['short']),*r['short'],file=out)
