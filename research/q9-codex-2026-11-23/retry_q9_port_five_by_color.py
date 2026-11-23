"""Run both remaining parity splits for the 98 previously undecided cases."""
import json
from pathlib import Path
from search_q9_bounded_edits import solve
from verify_q9_center_avoidance import verify

def splits(p):
    maj=p[0].bit_count()%2
    def order(a,b):
        return (b,a) if maj else (a,b)
    return [(order(2,3),order(2,3)),(order(3,2),order(2,3))]

def main():
    bank=[list(map(int,l.split())) for l in Path('q9_port_all_new_plateau.txt').read_text().splitlines()]
    ctrl=json.loads(Path('q9_independent_connectors_damaged_control.json').read_text())['source']
    for side in (0,1):
        n=(side,1-side);result=solve(ctrl,1,10000,(n,n))
        if result[-1]:break
    assert result[0]=='FOUND';print(json.dumps(['control',*result]),flush=True)
    for i,_,old,*_ in map(json.loads,open('q9_port_radius5_pairs.jsonl')):
        if i=='control' or old!='UNKNOWN':continue
        p=bank[i]
        for mode,counts in enumerate(splits(p)):
            st,domain,cuts,w=solve(p,5,60000,counts)
            print(json.dumps([i,mode,st,domain,cuts,w],separators=(',',':')),flush=True)
            if w:
                verify(w);assert len(w)==193;return
if __name__=='__main__':main()
