from pathlib import Path
import sys,json
D=Path(__file__).resolve().parent;B=D.parent/'q9_fourcross_new94';sys.path.insert(0,str(B));import whole
whole.D=D;r=json.loads((D/'cases.json').read_text())[1];q,s=whole.load(B/'spliced.dat')[1];hint={v-256 for v in r['hint'] if v>=256}
import os
hints=[list(map(int,line.split()))[5:] for line in (D/os.environ['HINT']).read_text().splitlines()] if os.getenv('HINT') else []
for c in (0,1):
    if hints:hint={v-256 for v in hints[c%len(hints)] if v>=256}
    whole.run(q,s,int(sys.argv[1]),c,int(sys.argv[2]),1,sys.argv[3],hint)
