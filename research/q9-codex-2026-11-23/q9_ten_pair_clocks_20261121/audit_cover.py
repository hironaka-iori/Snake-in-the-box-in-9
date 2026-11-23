"""Verify a cached UNSAT subwalk covers each surviving starting position."""
import json,random,sys
from collections import Counter
from functools import lru_cache
from pathlib import Path
D=Path(__file__).resolve().parent
def canonical(s):
    def relabel(word):
        seen='';r=[]
        for c in word:
            if c=='4':r.append('4');continue
            if c not in seen:seen+=c
            r.append(str(seen.index(c)))
        return ''.join(r)
    return min(relabel(s),relabel(s[::-1]))
def main(check_sat):
    ledger=[json.loads(line) for line in (D/'cover192.jsonl').open()]
    failed=set(); positive=0
    for rec in ledger:
        if rec['status']=='UNSAT':failed.add(canonical(''.join(str(int(d)//2) for d in rec['word'])))
        if rec.get('path'):positive+=1
    independent=Counter()
    if check_sat:
        from lazy import solve
        for r in random.Random(68123).sample([r for r in ledger if r['status']=='UNSAT'],128):
            s,*_=solve(r['word'],100000);independent[s]+=1
        assert independent=={'UNSAT':128}
    covered=Counter(); longest=0; lengths=Counter(); checked=Counter()
    @lru_cache(maxsize=262144)
    def supported(g):return canonical(g) in failed
    for line in (D/'all192.logtmp').open():
        row,ix,mp,w,rg=line.split()
        ss=[]
        for q in rg.rstrip(',').split(','):
            a,b=map(int,q.split('-'));ss.extend(range(a,b+1))
        g=''.join(str(int(x)//2) for x in w)
        pending=ss[:]
        while pending:
            first=pending[0];hi=next((i for i,q in enumerate(pending) if q-first>26),len(pending))
            batch=pending[:hi];pending=pending[hi:];stack=[batch]
            while stack:
                v=stack.pop();piece=g[max(v):min(v)+192]
                if supported(piece):
                    covered[int(row)]+=len(v);lengths[len(piece)]+=len(v)
                elif len(v)>1:stack.extend([v[:len(v)//2],v[len(v)//2:]])
                else:checked['uncovered']+=1
        checked['total']+=len(ss)
    print(json.dumps(dict(dictionary=len(ledger),distinct_unsat=len(failed),positive_targets=positive,independent_unsat_replays=dict(independent),total=checked['total'],covered=sum(covered.values()),uncovered=checked['uncovered'],by_donor=covered,blocking_lengths=[min(lengths),max(lengths)]),indent=2))
if __name__=='__main__':main('--sat' in sys.argv)
