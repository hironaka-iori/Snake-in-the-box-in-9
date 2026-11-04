"""Prepare a scaled retuning of the preserved158 experiment."""
from pathlib import Path
import ast, hashlib, json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/158-memory-bounded-floor-test'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True)
    b=s.encode() if isinstance(s,str) else s
    if p.exists():assert p.read_bytes()==b,p
    else:p.write_bytes(b)
def replace(s,a,b):
    assert s.count(a)==1,(a,s.count(a))
    return s.replace(a,b)
write(H/'.gitattributes','* -text\n')
for name in ['reconstruct_mapped.py','native_resources.py','native_guard_v5.py']:
    write(H/'scripts'/name,(P/'scripts'/name).read_bytes())
for name in ['potential_range_v5.py','run_potential_v5.py']:
    s=(P/'scripts'/name).read_text()
    s=replace(s,"    temporary.write_text(json.dumps(value, indent=2)+'\\n', encoding='utf-8', newline='\\n')\n    for attempt in range(40):\n        try:\n            temporary.replace(path)","    for attempt in range(40):\n        try:\n            temporary.write_text(json.dumps(value, indent=2)+'\\n', encoding='utf-8', newline='\\n')\n            temporary.replace(path)")
    if name.startswith('potential'):
        s=replace(s,'    def scan(potential):','    def scan(potential, mean=496):')
        s=replace(s,'potential[v[lo:hi]]-496','potential[v[lo:hi]]-mean')
        s=replace(s,"    save(run / 'graph-reconstruction.json', build)","    assert build['weight_sha256'] == '22497b6436475fbd248e456d87ed9e7eb7ac4cf9d78ef2804704f1ef905024b2'\n    save(run / 'graph-reconstruction.json', build)")
        prefix,tail=s.split("    journal = run / 'journal'; journal.mkdir()",1)
        prefix += "    weights *= 9\n    build['scaled_weight_sha256'] = array_sha(weights)\n    save(run / 'graph-reconstruction.json', build)\n    journal = run / 'journal'; journal.mkdir()"
        tail=tail.replace('496','4462').replace('603','5409').replace('631','5413').replace('632','5414')
        tail=tail.replace('PASS_MINIMUM_RANGE_AT_MEAN4462','PASS_MINIMUM_SCALED_RANGE_AT_MEAN4462')
        tail=replace(tail,'certificate = scan(selected)','certificate = scan(selected, mean=4462)')
        tail=replace(tail,'mean=4462, occurrence_credit=0','scaled_mean=4462, scale=9, mean="4462/9", occurrence_credit=0, rounding_loss_assumed=4')
        tail=replace(tail,'range_change_from156=None if selected_range is None else selected_range-602,','original156_range=602,')
        tail=replace(tail,'Fraction(1098960+8*4462+selected_range, 4696)','Fraction(9*1098960+8*4462+selected_range-180, 9*4200+4462)')
        tail=replace(tail,'weight=int(weights[e]),','weight=int(weights[e])//9, scaled_weight=int(weights[e]),')
        tail=replace(tail,"primary_target='A potential at mean4462 with integer range at most5413'","primary_target='A potential for 9w at mean4462 with integer range at most5413'")
        s=prefix+tail
    else:
        s=replace(s,"default='floor17-range496'","default='scaled-floor17'")
        s=replace(s,'mean=496, occurrence_credit=0, new_global_bound=False','scaled_mean=4462, scale=9, maximum_scaled_range=5413, rounding_loss_assumed=4, occurrence_credit=0, new_global_bound=False')
    ast.parse(s)
    write(H/'scripts'/name,s)
prep=json.loads((P/'data/preparation_v5.json').read_text())
prep['script_pins']={p.relative_to(R).as_posix():sha(p) for p in sorted((H/'scripts').glob('*.py'))}
prep['adaptation']=dict(source_worker_sha256=sha(P/'scripts/potential_range_v5.py'),scale=9,mean=4462,maximum_range=5413,loss_assumed=4,new_global_bound=False)
write(H/'data/preparation_v5.json',json.dumps(prep,indent=2)+'\n')
print('PREPARED_SCALED_RETUNING')
