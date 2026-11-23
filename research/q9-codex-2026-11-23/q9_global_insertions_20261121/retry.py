from search import *
import sys
L=int(sys.argv[1]);guard=int(sys.argv[2])
words=(here.parent/f'q9_gap_generations/prior{L}.words').read_text().splitlines()
seen=set()
for f in sorted(here.glob(f'run{L}_*.jsonl')):
    for record in map(json.loads,f.read_text().splitlines()):
        i,row,a,e,st,_,_,_=record
        key=row,tuple(a),tuple(e)
        if st!='UNKNOWN' or key in seen:continue
        seen.add(key);st,c,w,loc=encode(words[row],a,e,guard)
        print(json.dumps([f.name,i,row,a,e,st,c,loc,w],separators=(',',':')),flush=True)
        if w:break
