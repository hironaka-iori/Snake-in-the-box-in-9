import json,sys
from run import *
for label in ('singlewide','doublewide'):
    cases=[json.loads(l) for l in (D/f'{label}.jsonl').read_text().splitlines()]
    prior=[dict((r[0],r[2]) for r in map(json.loads,(D/f'{label}-{s}.jsonl').read_text().splitlines())) for s in ('cadical','minicard')]
    for i,c in enumerate(cases):
        if any(p[i]=='UNSAT' for p in prior):continue
        fixed=unpack(int(c['fixed'],16));hint=set(bank[c['row']])|unpack(int(c['protected'],16))
        st,w=solve(fixed,hint,192,160000,'cadical')
        if w:check(w);assert len(w)>=193 and fixed<=set(w)
        print(json.dumps([label,i,st,w],separators=(',',':')),flush=True)
        if w:sys.exit()
