import json
from connect import repair
from prepare import D,words,majority
for j,(i,c) in enumerate(map(json.loads,(D/'broadfamilies.jsonl').read_text().splitlines())):
    st,B=repair(majority(words[c['row']]),c,14000)
    print(json.dumps([j,i,st,B],separators=(',',':')),flush=True)
