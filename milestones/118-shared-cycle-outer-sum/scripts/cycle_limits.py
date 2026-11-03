"""Upper limits from retained cycles under two unproved total-count hypotheses."""
from pathlib import Path
from fractions import Fraction
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/117-cycle-sum-refinement/data/graph-audit.json'
d=json.loads(source.read_text());rows=[]
for p in d['profiles']:
    assert p['all_saved_cycle_rule_deficits_zero']
    changes=[];gain=0
    for e in p['cycle']:
        extra=0
        for w in e['placements']:
            if w['canonical_shape']!=[0,1,2,3,0,1]:continue
            c=w['counts'];middle=c[2]
            lower=19 if middle>=6 else 18
            deficit=max(0,lower-sum(c))
            assert not (deficit and all(x<6 for x in c)), 'Old cycle would be removed'
            if w['offset']==1:extra=max(extra,deficit)
            changes.append(dict(edge=e['edge'],offset=w['offset'],counts=c,assumed_lower=lower,deficit=deficit))
        gain+=extra
    assert gain==({'completed':2,'conditional_floor18':1}[p['profile']])
    q=Fraction(p['weight_sum']+24*gain,p['cycle_length'])
    target=235 if p['profile']=='completed' else 234
    margin=(1098960-4200*target)*q.denominator-(target-8)*q.numerator
    assert margin>0
    rows.append(dict(profile=p['profile'],cycle_length=p['cycle_length'],old_weight_sum=p['weight_sum'],
        suffix_deficit_sum=gain,maximum_total_coefficient=24,maximum_cycle_mean=str(q),
        zero_range_comparison=str(Fraction(1098960*q.denominator+8*q.numerator,4200*q.denominator+q.numerator)),
        cannot_exclude_length=target,scaled_comparison_margin=margin,windows=changes))
out=dict(status='PASS_CONDITIONAL_SAVED_CYCLE_LIMITS',profiles=rows,
    assumptions=['Unrestricted 012301 total at least18','For012301 with middle at least6, total at least19'],
    coefficient_argument='4a+c<=120 implies min(a,c)<=24. Use maximum applicable deficit, never their sum.',
    graph_audit_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='No new rule is asserted. Retained old cycles give ceilings for a hypothetical extension of the fixed rule family. They do not establish new minimum means, potentials, or global bounds.')
p=H/'data/cycle-limits.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
for r in rows:print(r['profile'],r['maximum_cycle_mean'],'cannot exclude',r['cannot_exclude_length'],'margin',r['scaled_comparison_margin'])
