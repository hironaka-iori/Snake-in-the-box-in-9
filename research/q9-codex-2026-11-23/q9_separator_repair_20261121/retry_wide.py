import json,sys
from prepare import D,words,majority
from solve import solve
from collections import Counter
roots=list(map(json.loads,(D/'broadfamilies.jsonl').read_text().splitlines()))
und=[r[0] for r in map(json.loads,(D/'wide.jsonl').read_text().splitlines()) if r[2]=='UNKNOWN']
for j in und[::3]:
    i,c=roots[j];st,cut,conf,w=solve(majority(words[c['row']]),c,36000)
    print(json.dumps([j,st,cut,conf,w],separators=(',',':')),flush=True)
    if w:break
