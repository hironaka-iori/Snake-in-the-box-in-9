import json
from collections import Counter
from pathlib import Path
from search import norm,old_keys,vertices
from check import check
here=Path(__file__).resolve().parent
words=(here.parent/'q9_three_axis.in').read_text().splitlines()
summary={}
for d in (4,5):
    prior=old_keys(d);first={};hops=[];observed=[];initial=Counter()
    inputs=set()
    for f in here.glob(f'd{d}_*.jsonl'):
        for i,row,axes,H,k,s,c,w in map(json.loads,f.read_text().splitlines()):
            sig=norm(words[row],axes);assert sig not in prior
            first.setdefault(sig,set()).add(s);initial[s]+=1;hops.append(H);inputs.add(row)
            if w:assert len(w)==193 and check(w)==0
    cnf=Counter();fresh=0;pair=Counter();resolved={k for k,v in first.items() if 'UNSAT' in v}
    for record in map(json.loads,(here/f'independent{d}.jsonl').read_text().splitlines()):
        if record[0]=='control':
            assert record[2]=='FOUND' and len(record[3])==192 and check(record[3])==0
            continue
        fn,i,row,axes,s,t,w=record
        key=norm(words[row],axes);observed.append(key);cnf[t]+=1;pair[s+'/'+t]+=1
        if t=='UNSAT':
            if key not in resolved:fresh+=1
            resolved.add(key)
        if w:assert check(w)==0 and len(w)==193
    assert len(observed)==len(set(observed))==len(first)
    deep=Counter();added=0
    if d==5:
        for row,axes,H,r,s,c,w in map(json.loads,(here/'deep5.jsonl').read_text().splitlines()):
            deep[s]+=1;k=norm(words[row],axes)
            if s=='UNSAT' and k not in resolved:added+=1;resolved.add(k)
            if w:assert len(w)==193 and check(w)==0
    final=Counter();extra=0
    if d==5:
        for row,axes,H,r,s,c,w in map(json.loads,(here/'remaining5.jsonl').read_text().splitlines()):
            final[s]+=1;k=norm(words[row],axes)
            if s=='UNSAT' and k not in resolved:extra+=1;resolved.add(k)
            if w:assert len(w)==193 and check(w)==0
    summary[str(d)]=dict(final_retry=dict(final),additional_final=extra,prior_replayed=len(prior),rows_tested=len(inputs),trials=len(hops),distinct=len(first),first=dict(initial),
        free_steps=[min(hops),max(hops)],independent=dict(cnf),paired=dict(pair),additional_independent=fresh,deep=dict(deep),
        additional_deep=added,combined_unsat=len(resolved),remaining=len(first)-len(resolved),
        source_chords=dict(Counter(check(vertices(words[r])) for r in sorted(inputs))))
print(json.dumps(summary,indent=2))
