"""Search the replacement cycle for direct count or forced-share improvements."""
from pathlib import Path
import itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import credit
result=json.loads((HERE/'data/shares-analysis.json').read_text());cycle=result['cycle'];L=len(cycle)
signatures={}
for w in model.words(11):
    sig=tuple(model.canon(w[j:j+9]) for j in range(3));signatures.setdefault(sig,[]).append(w)
NB=[{v^(1<<d) for d in range(9)} for v in range(512)]
rows=[]
for i,e in enumerate(cycle):
    sig=tuple(tuple(cycle[(i+j-2)%L]['directions']) for j in range(3));poss=signatures.get(sig,[])
    # Empty matches indicate a geometric incompatibility, not permission to guess a word.
    values=[]
    for word in poss:
        W=[0]
        for d in word:W.append(W[-1]^(1<<d))
        selected=set(W);D=set.union(*(NB[v] for v in W[1:-1]))-selected
        D|={q for q in range(512) if len(NB[q]&selected)>=3}
        lower=[]
        for j in range(5,11):
            free=set(range(9))-{word[j-1],word[j]}
            K={W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(free,2)}
            lower.append(len(K&D))
        violations=[k for k,(b,c) in enumerate(zip(lower,e['counts'])) if c<6 and b>c]
        values.append(dict(directions=word,forced_counts=lower,violations=violations,share_lower=credit(W[6:11],D)))
    rows.append(dict(phase=i,counts=e['counts'],current_share=e['weight']-120*e['counts'][-1],
        realizations=values,all_directly_excluded=bool(values) and all(v['violations'] for v in values),
        minimum_share=min((v['share_lower'] for v in values),default=None)))
out=dict(cycle_length=L,phases=rows,excluded_phases=[r['phase'] for r in rows if r['all_directly_excluded']],
    share_improvement_phases=[r['phase'] for r in rows if r['minimum_share'] is not None and r['minimum_share']>r['current_share']],
    scope='Candidate geometric deductions on replacement-cycle windows. No new Lean theorem or graph deletion follows until checked.')
(HERE/'data/replacement-cycle-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='phases'})
