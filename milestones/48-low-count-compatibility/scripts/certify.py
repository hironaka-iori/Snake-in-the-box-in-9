"""Certify two joint inequalities and an asymmetric low-count exclusion."""
from pathlib import Path
import importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
for d in ['lean','logs','data','build','certificates']:(HERE/d).mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('jointcert',ROOT/'milestones/41-joint-intervening-sum/scripts/certify.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
p.HERE=HERE;p.old.HERE=HERE
rows=json.loads((HERE/'data/shortened.json').read_text())
for number,phase in [(481,8),(482,3)]:
    row=next(r for r in rows if r['phase']==phase)
    p.DIRS=row['directions'];p.BOUNDS=[(0,21)]*(len(p.DIRS)-1)
    p.build(number,row['positions'],row['joint_cap'],str(HERE/f'data/minimal-{phase}.json'))
row=next(r for r in rows if r['phase']==5)
p.old.build(483,dict(dirs=row['directions'],bounds=[(0,c) for c in row['caps']]))
