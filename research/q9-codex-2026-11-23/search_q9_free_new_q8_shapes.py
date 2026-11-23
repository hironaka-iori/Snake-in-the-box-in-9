"""Embed each new arm intact in Q9, leaving both facets free outside the arm."""
from pathlib import Path
from search_q9_long_arm_anywhere import work
from verify_q9_center_avoidance import forms,verify
from concurrent.futures import ProcessPoolExecutor
import json,sys
if __name__=='__main__':
    if len(sys.argv)<2:raise SystemExit('supply arm bank files')
    bank={}
    for filename in sys.argv[1:]:
        for seq in Path(filename).read_text().split():
            if len(seq)<96:continue
            p=[0]
            for d in seq:p.append(p[-1]^(1<<int(d)))
            verify(p)
            key=forms(p,len(seq))[0]
            bank.setdefault(key,p)
    old=set()
    for file in ['q9_long_arm_anywhere_atleast192.jsonl','q9_bitterman_free_192.jsonl','q9_bitterman_trims96_free_192.jsonl']:
        for line in Path(file).read_text().splitlines():
            r=json.loads(line)
            if isinstance(r,list):old.add((r[0],r[1],r[2]))
    jobs=[(k,p,e,g) for k,p in sorted(bank.items(),key=lambda kv:-len(kv[0])) for e,g in [(0,192),(1,192),(0,193)] if (k.hex(),e,g) not in old]
    print(json.dumps({'unique_arms':len(bank),'jobs':len(jobs)}),flush=True)
    with ProcessPoolExecutor(2) as pool:
        for r in pool.map(work,jobs,chunksize=1):
            print(json.dumps(r,separators=(',',':')),flush=True)
            if r[-1]:break
