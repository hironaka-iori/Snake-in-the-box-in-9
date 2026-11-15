"""Prepare one final native query with proved necessary visit inequalities."""
from pathlib import Path
H=Path(__file__).resolve().parents[1];P=H.parent/'229-two-layer-construction'
(H/'data/coverage46.json').write_bytes((P/'data/coverage46.json').read_bytes())
s=(P/'scripts/joint_free.py').read_text(encoding='utf-8')
guard="""assert a.width==46
two=json.loads((H/'data/coverage-two46.json').read_bytes())
prior=json.loads((H/'data/free-summary.json').read_bytes())
four=json.loads((H/'data/coverage46.json').read_bytes())
assert two['status']=='COMPLETE_NATIVE_EXCLUSION' and two['total_crossings']==2
assert four['status']=='COMPLETE_NATIVE_EXCLUSION' and not prior['six_unresolved_after_free']
for cover in [two,prior,four]:assert all(sha(p)==h for p,h in cover['pins'].items())
assert set(map(int,a.ids.split(',')))<=set(prior['unresolved'])
"""
assert s.count('assert a.width==46\n')==1
s=s.replace('assert a.width==46\n',guard)
anchor='        all_cross_edges.extend(edges);crosses.append(len(edges))'
assert s.count(anchor)==1
s=s.replace(anchor,"""        upper_anchors=int(u>=256)+int(v>=256)
        model.add(3*sum(edges)<=2*sum(x[z] for z in values if z>=256)+upper_anchors)
        model.add(3*sum(edges)<=2*sum(x[z] for z in values if z<256)+2-upper_anchors)
"""+anchor)
anchor='    for u in variables[0]:'
assert s.count(anchor)==1
s=s.replace(anchor,"""    fixed=4-row['replacement_crossings'];assert fixed>=1
    model.add(sum(all_cross_edges)+fixed>=8)
"""+anchor)
s=s.replace('No total crossing count is prescribed.','No exact total crossing count is prescribed. Complete native same-context2/4/6 exclusions and endpoint parity impose total>=8. Each replacement satisfies3c<=2u+r and3c<=2l+2-r; written path-to-run extraction remains outside Lean.')
(H/'scripts/joint_visits.py').write_text(s,encoding='utf-8')
s=(P/'scripts/run_free.py').read_text(encoding='utf-8').replace('joint_free.py','joint_visits.py')
old="H/'data'/f'regions{width}.json']";assert s.count(old)==1
s=s.replace(old,"H/'data'/f'regions{width}.json', H/'data/coverage-two46.json', H/'data/free-summary.json', H/'data/coverage46.json', H/'lean/FaceVisits230.lean', H/'data/FaceVisits230-audit.json']")
(H/'scripts/run_visits.py').write_text(s,encoding='utf-8')
print('VISIT_WORKER_PREPARED')
