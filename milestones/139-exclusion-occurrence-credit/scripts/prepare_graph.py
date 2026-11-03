"""Derive the credit83/3 experiment from the pinned milestone131 evaluator."""
from pathlib import Path
import ast,hashlib,json,itertools
from fractions import Fraction
H=Path(__file__).resolve().parents[1];ROOT=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=ROOT/'milestones/131-odd-pair-six-count/scripts/evaluate_graph.py'
assert sha(src)=='86386a1a117dfd9080b7360f9b99a641054fe9ea174baa9a2b532b33199e52ac'
s=src.read_text(encoding='utf-8')
def change(a,b):
 global s
 assert s.count(a)==1,(a[:80],s.count(a))
 s=s.replace(a,b)
s=s.replace('SNAKE131_PARENT_PID','SNAKE139_PARENT_PID').replace('odd-pair9-six25','exclusion-credit83')
change("if not _args.worker:\n    _folder.mkdir", """if not _args.worker:
    try:
        _resources({os.getpid()})
    except AssertionError as gate:
        print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE',reason=str(gate))),flush=True)
        raise SystemExit(0)
    _folder.mkdir""")
insert=r'''
# Reproduce the immediate predecessor before applying any new rule.
previous131=read('milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json')
assert previous131['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
previous131_profiles={x['profile']:x for x in previous131['profiles']}
old_removed=read('milestones/131-odd-pair-six-count/data/odd-pair9-six25/removed-indices.json')
assert np.array_equal(np.flatnonzero(~mask),np.array(old_removed))
assert int(mask.sum())==previous131['edges']
for name in ['completed','conditional_floor18']:
    assert sha((base_weights[name]+shared)[mask].tobytes())==previous131_profiles[name]['weight_sha256']
for rel in ['milestones/138-seven-cycle-endpoints/data/proof-completion.json',
 'milestones/138-seven-cycle-endpoints/data/ActualBase138Minimal-audit.json',
 'milestones/138-seven-cycle-endpoints/lean/ActualBase138Minimal.lean',
 'milestones/137-actual-block-assembly/data/verification.json',
 'milestones/137-actual-block-assembly/data/ActualCount137-audit.json',
 'milestones/137-actual-block-assembly/lean/ActualCount137.lean',
 'milestones/138-seven-cycle-endpoints/data/Credit138-audit.json',
 'milestones/138-seven-cycle-endpoints/lean/Credit138.lean',
 'milestones/139-exclusion-occurrence-credit/scripts/prepare_graph.py']:
    pins[rel]=sha((ROOT/rel).read_bytes())
proof=read('milestones/138-seven-cycle-endpoints/data/proof-completion.json')
assert proof['status']=='PASS_ACTUAL_NINE_TRANSITION_EXCLUSION_AND_CONDITIONAL_ARITHMETIC'
assert sha((ROOT/'milestones/138-seven-cycle-endpoints/lean/ActualBase138Minimal.lean').read_bytes())==proof['final_source_sha256']
occurrences=read('milestones/137-actual-block-assembly/data/verification.json')
assert occurrences['checked_total_low_pair_window_bound']==24 and occurrences['actual_occurrence_bound_lean_checked']
old_mask=mask.copy()
new_shape=np.array([canon(word)==(0,1,2,3,0,1,4,3,0) for word in ds])[arrays['direction']]
new_reject=new_shape & np.all(digits==np.array([6,3,3,3,5,2]),axis=1)
mask &= ~new_reject
# Only exact stored counts may certify the low-pair event.
suffix_shape=np.array([shape(word[3:9])==(0,1,2,0,3,2) for word in ds])[arrays['direction']]
a,b=digits[:,2],digits[:,4]
event=suffix_shape & (a<6) & (b<6) & (a+b<=9)
assert not np.any(event & mask & (a+b<9))
assert old_mask[992157] and not mask[992157] and mask[1273862]
four_ids=np.array([e['edge'] for e in previous131_profiles['completed']['cycle']])
assert len(four_ids)==4 and np.all(mask[four_ids]) and int(event[four_ids].sum())==2
'''
change('ids = np.flatnonzero(mask)',insert+'\nids = np.flatnonzero(mask)')
change("assert saved_mean == Fraction(3011,6), 'Saved18-cycle comparison changed'",
"""assert saved_mean == Fraction(3011,6), 'Saved18-cycle comparison changed'
assert not np.any(event[saved_ids])
assert Fraction(int((3*(base_weights['completed']+shared)+83*event)[four_ids].sum()),12)==Fraction(3011,6)
assert np.array_equal(mask,old_mask & ~new_reject)""")
change("W = (base_weights[name]+shared)[mask]","W = (3*(base_weights[name]+shared)+83*event)[mask]")
change('bound = Fraction(1098960*d+8*p+R,4200*d+p)',
 'bound = Fraction(3*1098960*d+8*p+24*83*d+R,3*4200*d+p)')
change("counts=digits[k].tolist(),weight=int(W[e]),base_weight=int(base_weights[name][k]),",
"""counts=digits[k].tolist(),weight=int(W[e]),base_weight=int(base_weights[name][k]),
            weight_multiplier=3,occurrence_event=bool(event[k]),occurrence_credit_scaled=83*int(event[k]),""")
change("row = dict(profile=name,mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,",
"""row = dict(profile=name,mean=str(mu/3),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,3*d)),cycle=cycle,
        weight_multiplier=3,credit='83/3',occurrence_allowance=24,
        target_mean_reached=mu/3>=Fraction(3011,6),target_range_reached=Fraction(R,3*d)<Fraction(7753,6),""")
change("zero_range_comparison=str(Fraction(1098960*d+8*p,4200*d+p))",
 "zero_range_comparison=str(Fraction(3*1098960*d+8*p+24*83*d,3*4200*d+p))")
change("print(name,'exact mean',mu,'range',Fraction(R,d),'conditional comparison',bound,flush=True)",
 "print(name,'exact mean',mu/3,'range',Fraction(R,3*d),'conditional comparison',bound,flush=True)")
change("coefficients=coefficients,rules=rules,inherited_pair_guards=pair_guards,",
"""coefficients=coefficients,rules=rules,inherited_pair_guards=pair_guards,
    predecessor131_reproduced=True,predecessor131_edges=int(old_mask.sum()),
    new_full_nine_rejections_total=int(new_reject.sum()),
    new_full_nine_rejections_on_predecessor=int((new_reject&old_mask).sum()),
    occurrence_events_retained=int(event[mask].sum()),weight_multiplier=3,
    credit='83/3',occurrence_allowance=24,
    event_rule='Suffix012032, both pair symbols below6, sum at most9; prefix representations never counted.',
    new_exclusion_rule='Forward full-nine012301430 with symbols6,3,3,3,5,2; no reversal of missing count data.',
""")
change("No new unconditional or conditional actual-snake upper bound is claimed.",
 "The new exclusion and occurrence allowance are proved for actual snakes; inherited local hypotheses and graph assembly remain pending. No new actual-snake upper bound is claimed.")
ast.parse(s)
target=H/'scripts/evaluate_graph.py';assert not target.exists();target.write_text(s,encoding='utf-8',newline='\n')
for a,b in itertools.product(range(1,22),repeat=2):
 x,y=min(a,6),min(b,6)
 assert not (x<6 and y<6 and x+y<=9) or a+b<=9
for p,d,rr in [(3011,2,0),(3011,2,7753),(1500,1,700)]:
 mu=Fraction(p,3*d);rang=Fraction(rr,3*d)
 assert (Fraction(1098960)+8*mu+24*Fraction(83,3)+rang)/(4200+mu)==Fraction(3*1098960*d+8*p+24*83*d+rr,3*4200*d+p)
out=dict(status='PREPARED_NOT_RUN',source_sha256=sha(src),prepare_sha256=sha(Path(__file__)),evaluate_sha256=sha(target),weight_multiplier=3,credit='83/3',occurrence_allowance=24,clipping_cases=441,profiles=['completed','conditional_floor18'],scope='Preparation and exact algebra only. Both profiles retain131 hypotheses; even-length upper bounds are not inferred from the odd-length model.')
(H/'data/preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
