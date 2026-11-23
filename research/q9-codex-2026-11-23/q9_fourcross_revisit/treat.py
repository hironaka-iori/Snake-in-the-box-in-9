from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent;B=D.parent/'q9_fourcross_new94';sys.path.insert(0,str(B));import whole
whole.D=D
r=json.loads((D/'cases.json').read_text())[0];hint={v-256 for v in r['hint'] if v>=256}
target=int(sys.argv[1]);budget=int(sys.argv[2]);prefix=sys.argv[3];sets=[]
for i in (0,1):
    for q,s in whole.load(D/f'fullalt_{i}.dat'):
        sets.append((q,s))
if len(sys.argv)>4:choice=list(map(int,sys.argv[4:]))
else:choice=list(range(len(sets)))
for i in choice:
    q,s=sets[i]
    for c in (0,1):whole.run(q,s,target,c,budget,i,prefix,hint)
