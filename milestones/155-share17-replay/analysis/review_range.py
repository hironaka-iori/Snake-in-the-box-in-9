"""Review saved cycle rows and exact arithmetic without invoking a solver."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib, json

A=Path(__file__).resolve().parent; H=A.parent; R=H.parents[1]
paths=[R/p for p in [
    'milestones/153-pair-conditioned-share17/audit/pair-query-and-cycle-review.json',
    'milestones/145-countfree-012301/data/joint-floor-analysis.json',
    'milestones/149-share-credit-tradeoff/audit/graph-review.json',
    'milestones/144-countfree-share18/data/share18-impact/removed-indices.json']]
j,k,old,removed=[json.loads(p.read_text(encoding='utf-8-sig')) for p in paths]

def canon(ds):
    labels={}; out=[]
    for x in ds:
        if x not in labels: labels[x]=len(labels)
        out.append(labels[x])
    return out

rows=j['cycles']['fourteen']['rows']; edges=[r['edge'] for r in rows]
assert edges==k['cycle_edges'] and len(rows)==14
assert not set(edges).intersection(removed)
matches=[]
for row in rows:
    for start in range(4):
        word=row['directions'][start:start+6]
        if canon(word)==[0,1,2,0,3,2] or canon(word[::-1])==[0,1,2,0,3,2]:
            matches.append([row['edge'],start])
assert not matches
case=next(x for x in k['comparisons'] if x['floor_012301']==x['floor_012340']==16)
weights=case['weights']
assert sum(weights)==6944 and sum(weights[:2])==512
mu=Q(sum(weights),14); rg=2*mu-512
bound=(1098960+8*mu+rg)/(4200+mu)
assert mu==496 and rg==480 and bound==Q(137926,587)==235-Q(19,587)
assert 7723488-32824*234==42672 and 2*234-13==455 and 234-10==224
assert Q(42672-455*16,224)==158
record=dict(
    status='PASS_SAVED_ROW_AND_EXACT_ARITHMETIC_REVIEW_LEAN_PENDING',
    source_files_sha256={p.relative_to(R).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in paths+[Path(__file__)]},
    fourteen_cycle_edges=edges, all_fourteen_edges_retained=True,
    all_placement_012032_matches=matches,
    weight_regime='Preserved145 affine profile, F>=11 and G>=4; all other cycle weights fixed.',
    F16_G16=dict(cycle_total=6944,mean_cap='496',two_edge_sum=512,
        comparison_lower_bound=str(bound),gap_below235='19/587',gap_above234='568/587'),
    target233_necessary_condition='455F +224G >42672 +168C',
    target233_F16_requires='G>158 if C>=0; this is necessary, never sufficient.',
    old149_cycle_removed_edges=old['removed_in_later144_graph']['three_cycle'],
    lean_checked=False,new_global_upper_bound=False,
    limitations=['Saved-row review reuses prior graph extraction; no new full-array audit.',
        'Changing or removing the fourteen cycle, its other weights, or the comparison invalidates this restriction.',
        'Local share17 completion is separately recorded.'])
(A/'range-scope-review.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print(record['status'])
