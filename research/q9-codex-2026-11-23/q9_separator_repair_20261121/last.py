import json,sys
from prepare import D,words,majority
from solve import solve
def read(f):return list(map(json.loads,(D/f).read_text().splitlines()))
name=sys.argv[1];parity=int(sys.argv[2]);out=[]
if name=='mosaic':
    plans=read('mosaic_plans.jsonl');out=[(r[0],plans[r[0]]) for r in read('mosaic.jsonl') if r[1]=='UNKNOWN']
else:
    plans=read('broadfamilies.jsonl');st={r[0]:r[2] for r in read('wide.jsonl')};st.update({r[0]:r[1] for r in read('sector_retry.jsonl')});out=[(i,plans[i][1]) for i in st if st[i]=='UNKNOWN']
for j,(i,c) in enumerate(out):
    if j%2!=parity:continue
    st,_,conf,w=solve(majority(words[c['row']]),c,60000)
    print(json.dumps([i,st,conf,w],separators=(',',':')),flush=True)
    if w:break
