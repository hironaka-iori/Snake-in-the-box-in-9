"""Retry the first 48 unresolved 5+4 cases at a larger conflict budget."""
import json
from pathlib import Path
from search import repair
here=Path(__file__).resolve().parent
seeds=[list(map(int,l.split())) for l in (here.parent/'q9_onechord_expanded_800.txt').read_text().splitlines()]
pending=[json.loads(l) for l in (here/'shape54.jsonl').read_text().splitlines() if json.loads(l)[4]=='UNKNOWN']
for original,row,masks,gauge,*_ in pending[:48]:
    st,w,c=repair(seeds[row],masks,gauge,60000)
    print(json.dumps([original,row,masks,gauge,st,c,w],separators=(',',':')),flush=True)
    if w:break
