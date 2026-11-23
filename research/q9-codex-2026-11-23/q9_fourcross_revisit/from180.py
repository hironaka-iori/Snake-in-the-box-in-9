from pathlib import Path
import json,sys
import strengthened,oddmodel
D=Path(__file__).resolve().parent;B=D.parent/'q9_fourcross_new94';r=json.loads((D/'cases.json').read_text())[1];hints=[list(map(int,l.split()))[5:] for l in (D/'improved180.paths').read_text().splitlines()];q,s=oddmodel.load(B/'spliced.dat')[1]
if sys.argv[1]=='joint':
    for c in (0,1):
        for m in (0,1):strengthened.search(0,1,q,s,r['anchor'],set(hints[c]),192,c,205000,'seed0joint192',m)
else:
    oddmodel.run(q,s,181,-1,220000,1,'new181',{v-256 for v in hints[int(sys.argv[1])] if v>=256})
