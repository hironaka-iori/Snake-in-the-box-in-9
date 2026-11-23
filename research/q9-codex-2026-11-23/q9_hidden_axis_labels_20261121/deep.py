from pathlib import Path
from search import solve
import json
here=Path(__file__).resolve().parent
words=(here.parent/'q9_three_axis.in').read_text().splitlines()
todo=[]
for f in sorted(here.glob('d5_*.jsonl')):
    for line in f.read_text().splitlines():
        i,row,axes,H,r,st,c,w=json.loads(line)
        if st=='UNKNOWN':todo.append((r/(H*(H+1)),row,axes,H,r))
todo.sort()
for _,row,axes,H,r in todo[:24]:
    st,c,w,_=solve(words[row],axes,100000)
    print(json.dumps([row,axes,H,r,st,c,w],separators=(',',':')),flush=True)
    if w:break
