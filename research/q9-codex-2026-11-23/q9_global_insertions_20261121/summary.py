from collections import Counter
from pathlib import Path
from math import comb
import json
from verify import vertices,validate
here=Path(__file__).resolve().parent
def key(r):return (r[1],tuple(r[2]),tuple(r[3]))
report={}
for L in (190,191):
    words=(here.parent/f'q9_gap_generations/prior{L}.words').read_text().splitlines()
    rows=[json.loads(l) for p in sorted(here.glob(f'run{L}_*.jsonl')) for l in p.read_text().splitlines()]
    init=Counter(r[4] for r in rows);ans={key(r):r[4] for r in rows};assert len(ans)==len(rows)
    for fn,i,row,axes,extra,st,c,loc,w in map(json.loads,(here/f'retry{L}.jsonl').read_text().splitlines()):
        k=(row,tuple(axes),tuple(extra));assert ans[k]=='UNKNOWN';ans[k]=st
        if w:validate(words[row],axes,extra,loc,st,w)
    complete={}
    more=[json.loads(l) for p in sorted(here.glob(f'all{L}_*.jsonl')) for l in p.read_text().splitlines()]
    for r in more:
        i,row,axes,extra,st,c,loc,w=r;k=key(r)
        complete.setdefault(k[:2],{})[k[2]]=st
        if w:validate(words[row],axes,extra,loc,st,w)
    assert all(len(v)==6**(192-L) for v in complete.values())
    combined={**ans}
    for r in more:
        k=key(r)
        if r[4]!='UNKNOWN' or k not in combined:combined[k]=r[4]
    report[L]=dict(source_rows=len(words),sampled_rows=len(set(r[1] for r in rows)),trials=len(rows),initial=dict(init),after_retry=dict(Counter(ans.values())),
        direction_complete_pairs=len(complete),direction_complete_unsat=sum(all(s=='UNSAT' for s in r.values()) for r in complete.values()),
        direction_records=len(more),direction_status=dict(Counter(r[4] for r in more)),union=dict(Counter(combined.values())),
        position_combinations=comb(192,192-L))
print(json.dumps(report,indent=2))
