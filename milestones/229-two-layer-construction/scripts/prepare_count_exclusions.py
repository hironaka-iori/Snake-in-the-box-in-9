"""Use completed crossing-count exclusions inside the larger construction search."""
from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/joint_free.py').read_text(encoding='utf-8')
anchor='assert a.width==46\n'
addition="""coverpath=H/'data/coverage46.json';cover=json.loads(coverpath.read_bytes())
assert cover['status']=='COMPLETE_NATIVE_EXCLUSION' and cover['width']==46 and cover['contexts']==315
assert all(sha(p)==h for p,h in cover['pins'].items())
sixpath=H/'data/six46.json';six=json.loads(sixpath.read_bytes());execution=json.loads((H/'data/six46-execution.json').read_bytes())
assert execution['status']=='ACCEPTED_NATIVE_RESULT' and execution['exit_code']==0 and execution['stop_reason'] is None
assert sha(sixpath)==execution['result_sha256'] and all(sha(p)==h for p,h in execution['pins'].items())
excluded_six={r['id'] for r in six['results'] if r['status']=='INFEASIBLE'}
assert len(excluded_six)==200 and six['witness'] is None
"""
assert s.count(anchor)==1;s=s.replace(anchor,anchor+addition,1)
anchor="    for u in variables[0]:\n"
addition="""    model.add(sum(all_cross_edges)!=row['replacement_crossings'])
    if row['id'] in excluded_six:model.add(sum(all_cross_edges)!=row['replacement_crossings']+2)
"""
assert s.count(anchor)==1;s=s.replace(anchor,addition+anchor,1)
old='No boundary-change cut or smaller-width exclusion is assumed.'
new='No boundary-change cut is imposed. The complete same-width four-crossing native cover forbids totalfour, and each completed same-context six-crossing result forbids totalsix. Other crossing counts remain permitted.'
assert old in s;s=s.replace(old,new)
p=H/'scripts/joint_count_exclusions.py';assert not p.exists();p.write_text(s,encoding='utf-8')
s=(H/'scripts/run_free.py').read_text(encoding='utf-8').replace('joint_free.py','joint_count_exclusions.py')
old="H/'data'/f'regions{width}.json']"
new="H/'data'/f'regions{width}.json', H/'data/coverage46.json', H/'data/six46.json', H/'data/six46-execution.json']"
assert old in s;s=s.replace(old,new)
(H/'scripts/run_count_exclusions.py').write_text(s,encoding='utf-8')
print('PREPARED_CONDITIONAL_COUNT_EXCLUSIONS')
