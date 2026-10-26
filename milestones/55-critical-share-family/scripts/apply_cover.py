"""Measure the selected share cover, keeping the numerical control comparison separate."""
from pathlib import Path
import importlib.util,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/54-share-coverage/scripts'))
import build
spec=importlib.util.spec_from_file_location('coverage_analyze',ROOT/'milestones/54-share-coverage/scripts/analyze.py')
analyze=importlib.util.module_from_spec(spec);spec.loader.exec_module(analyze)
build.HERE=HERE;analyze.HERE=HERE
prior=ROOT/'milestones/54-share-coverage'
keys=json.loads((prior/'data/combined-keys.json').read_text())['keys']
existing=json.loads((prior/'proposed-bidirectional/data/model.json').read_text())['share_rules'][4:]
windows=json.loads((HERE/'data/windows.json').read_text());cover=json.loads((HERE/'data/cycle-cover.json').read_text())
new=[]
for i in cover['share_only']['selected']:
    row=windows[i]
    for reverse in [False,True]:
        ds=row['directions'][::-1] if reverse else row['directions']
        cs=row['counts'][::-1] if reverse else row['counts']
        new.append(dict(directions=list(build.model.canon(ds)),counts=cs,lower=96,milestone=55,
                        status='NUMERICAL_ONLY',source=f'data/screen/w{i:02d}.json'))
build.build(keys,'covered',existing+new)
analyze.run('covered',True)
control_keys=sorted(set(build.key(ds,bounds) for ds,bounds in keys)|
    {build.key(windows[i]['directions'],[build.LUMP[c] for c in windows[i]['counts']]) for i in cover['ordinary_unsat']})
(HERE/'data/control-keys.json').write_text(json.dumps(dict(keys=control_keys),indent=2)+'\n')
build.build(control_keys,'count-control',existing)
analyze.run('count-control',True)
