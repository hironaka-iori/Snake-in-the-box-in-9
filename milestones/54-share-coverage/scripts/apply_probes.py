"""Measure numerical candidates without representing them as Lean theorems."""
import json
from build import HERE, LUMP, build, key

keys=json.loads((HERE/'data/all-keys.json').read_text())['keys']
windows=json.loads((HERE/'data/windows.json').read_text())
rules=[];ordinary=[]
for i,row in enumerate(windows):
    control=json.loads((HERE/f'data/controls/w{i:02d}.json').read_text())
    screen=json.loads((HERE/f'data/screen/w{i:02d}.json').read_text())
    if screen['status']=='INFEASIBLE':
        assert control['status']=='SAT'
        rules.append(dict(directions=row['directions'],counts=row['counts'],lower=96,
                          milestone=54,status='NUMERICAL_ONLY',source=f'data/screen/w{i:02d}.json'))
    if control['status']=='UNSAT':
        ordinary.append(key(row['directions'],[LUMP[c] for c in row['counts']]))
build(keys,'proposed-share',rules)
combined=sorted(set(key(ds,bounds) for ds,bounds in keys)|set(ordinary))
(HERE/'data/combined-keys.json').write_text(json.dumps(dict(keys=combined,
    added=ordinary,scope='Numerical exclusions discovered while checking ordinary controls.'),indent=2)+'\n')
build(combined,'proposed-joint',rules)
