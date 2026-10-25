"""Generate the joint-count certificate and arbitrary-coordinate theorem."""
from pathlib import Path
import importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('jointcert',ROOT/'milestones/41-joint-intervening-sum/scripts/certify.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE;p.old.HERE=HERE
p.DIRS=[0,1,2,3,4,0];p.BOUNDS=[(0,21)]*5
p.build(501,[1,4,5],12,str(HERE/'data/triple-sum-12.json'))
satfile=HERE/'lean/LocalWindowSat/JointIntervening501.lean'
satfile.write_text(satfile.read_text(encoding='utf-8').replace('[jointCentres, jointSum]','[jointCentres, jointSum, Nat.add_assoc]'),encoding='utf-8')
case=dict(number=501,kind='sum',dirs=p.DIRS,bounds=p.BOUNDS,positions=[1,4,5],cap=12,caps=None)
(HERE/'data/cases.json').write_text(json.dumps([case],indent=2)+'\n')
s=(ROOT/'milestones/48-low-count-compatibility/scripts/wrappers.py').read_text(encoding='utf-8-sig')
s=s[s.index('for case in cases[:2]:'):s.index("s='''import CycleExclusion483")]
s=s.replace("    s=f'''import", "    expression=' + '.join(f'coreAlpha p (r+{j})' for j in pos)\n    rewrites=','.join(f'h{j}' for j in pos)\n    s=f'''import")
s=s.replace('coreAlpha p (r+{pos[0]}) + coreAlpha p (r+{pos[1]})','{expression}')
s=s.replace('rw [h{pos[0]},h{pos[1]}]','rw [{rewrites}]')
exec(compile(s,'joint_wrapper_template','exec'),dict(HERE=HERE,ROOT=ROOT,cases=[case]))
