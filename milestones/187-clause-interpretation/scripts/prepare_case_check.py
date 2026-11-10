from pathlib import Path
import hashlib,json
H=Path('E:/Snake-in-a-box/milestones/187-clause-interpretation');name='BoundarySlackCases187'
assert not (H/'data'/(name+'-audit.json')).exists()
p=H/'lean'/(name+'.lean');s=p.read_text()
s=s.replace('  by_contra h\n  have hlarge : 234 ≤ m := by omega\n  have := five_slack_requires_small_loss m W L hlarge hb ht\n  have := hloss hlarge\n  omega',
'''  by_cases hlarge : 234 ≤ m
  · have := five_slack_requires_small_loss m W L hlarge hb ht
    have := hloss hlarge
    omega
  · omega''')
s=s.replace('  by_contra h\n  have hlarge : 234 ≤ m := by omega\n  have hl := five_slack_requires_small_loss m W L hlarge hb5 ht\n  have := (four_point_slack m W L hm (hb4 hl) ht).2\n  omega',
'''  by_cases hlarge : 234 ≤ m
  · have hl := five_slack_requires_small_loss m W L hlarge hb5 ht
    have := (four_point_slack m W L hm (hb4 hl) ht).2
    omega
  · omega''')
p.write_text(s,encoding='utf-8',newline='\n')
p=H/'data'/(name+'-execution.json');j=json.loads(p.read_text())
j['source_sha256'][name]=hashlib.sha256((H/'lean'/(name+'.lean')).read_bytes()).hexdigest()
p.write_text(json.dumps(j,indent=2)+'\n')
(H/'scripts/prepare_case_check.py').write_bytes(Path(__file__).read_bytes())
print('Prepared core-only case proof for sequential checking.')
