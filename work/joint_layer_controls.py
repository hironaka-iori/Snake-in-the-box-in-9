"""Exhaustive small-cube controls independent of the constraint model."""
import json
from pathlib import Path
from joint_layer_search import solve


def paths(n):
    by_length={}
    def visit(p):
        by_length.setdefault(len(p)-1,[]).append(frozenset(p))
        for k in range(n):
            v=p[-1]^(1<<k)
            if v not in p and all((v^w).bit_count()!=1 for w in p[:-1]):
                visit(p+[v])
    visit([0]);return by_length

if __name__=='__main__':
    results=[]
    for n in [2,3]:
        bank=paths(n)
        for left in range(1,max(bank)+2):
            for right in range(left,max(bank)+2):
                expected=any(a&b=={0} for a in bank.get(left,[]) for b in bank.get(right,[]))
                for symmetry in [False,True]:
                    result=solve(n,left,right,5,workers=1,symmetry=symmetry)
                    assert result['status'] in ['OPTIMAL','FEASIBLE','INFEASIBLE'],result
                    assert (result['status']!='INFEASIBLE')==expected,result
                    results.append({'n':n,'left':left,'right':right,'symmetry':symmetry,
                                    'exhaustive_feasible':expected,'solver_status':result['status']})
    Path('outputs/joint_layer_controls.json').write_text(json.dumps({'all_matched':True,'cases':results},indent=2),encoding='utf-8')
    print(f'All {len(results)} comparisons matched exhaustive small-cube enumeration.')
