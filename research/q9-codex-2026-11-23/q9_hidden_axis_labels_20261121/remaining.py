from pathlib import Path
import json
from search import solve,norm
here=Path(__file__).resolve().parent
words=(here.parent/'q9_three_axis.in').read_text().splitlines()
known=set();jobs=[]
for f in here.glob('d5_*.jsonl'):
    for i,row,axes,H,r,st,conf,_ in map(json.loads,f.read_text().splitlines()):
        key=norm(words[row],axes)
        if st=='UNSAT':known.add(key)
        else:jobs.append((row,axes,H,r))
for rec in map(json.loads,(here/'independent5.jsonl').read_text().splitlines()):
    if rec[0]!='control' and rec[5]=='UNSAT':known.add(norm(words[rec[2]],rec[3]))
for row,axes,H,r,st,conf,_ in map(json.loads,(here/'deep5.jsonl').read_text().splitlines()):
    if st=='UNSAT':known.add(norm(words[row],axes))
for row,axes,H,r in jobs:
    if norm(words[row],axes) in known:continue
    st,c,w,_=solve(words[row],axes,250000)
    print(json.dumps([row,axes,H,r,st,c,w],separators=(',',':')),flush=True)
    if w:break
