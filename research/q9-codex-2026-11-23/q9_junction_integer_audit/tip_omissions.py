"""Test every single deletion from the 75-pin set by replaying bounds obtained with all pins."""
import json
from pathlib import Path
from verify import HERE, ROOT, close, rows, value

def main():
    orig=set(rows(ROOT/'q9_junction_first_omission.jsonl')[0]['fixed'])
    cs=[json.loads((HERE/'unbounded_duals'/f'all75_h{h}_n16.json').read_text()) for h in range(3)]
    for v in sorted(orig):
        rec=[]
        for h,c in enumerate(cs):
            p,d=close(orig-{v},set(),None,h)
            g,e=(193,0) if h==2 else (192,h)
            n=value(c,p,d,g,e)
            rec.append(n)
        print(json.dumps({'omission':v,'numerators':rec,'excludes':all(n<(194 if h==2 else 193)*10000 for h,n in enumerate(rec))}),flush=True)

if __name__=='__main__':main()
