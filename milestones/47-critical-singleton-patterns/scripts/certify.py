"""Generate three ordinary count-one exclusions from necessary path clauses."""
from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('ordinary',ROOT/'milestones/38-four-position-obstruction/scripts/certify.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE
for d in ['data','logs','lean','certificates','build']:(HERE/d).mkdir(exist_ok=True)
cases=[]
for number,phase in [(471,0),(472,2),(473,8)]:
    r=next(r for r in json.loads((HERE/'data/minimal-patterns.json').read_text()) if r['phase']==phase)
    assert r['cycle_cuts']==[]
    case=dict(number=number,dirs=r['directions'],position=r['position'],bounds=[(0,x) for x in r['caps']])
    p.build(number,case);cases.append(case)
(HERE/'data/cases.json').write_text(json.dumps(cases,indent=2)+'\n')
