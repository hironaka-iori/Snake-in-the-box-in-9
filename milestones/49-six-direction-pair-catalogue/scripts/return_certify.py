from pathlib import Path
import importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('jointcert',ROOT/'milestones/41-joint-intervening-sum/scripts/certify.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE;p.old.HERE=HERE
p.DIRS=[0,1,2,0];p.BOUNDS=[(0,21)]*3
p.build(4934,[1,3],4,str(HERE/'data/four-step-return-sum4.json'))
case=dict(number=4934,kind='sum',dirs=p.DIRS,bounds=p.BOUNDS,positions=[1,3],cap=4,caps=None)
(HERE/'data/return-case.json').write_text(json.dumps(case,indent=2)+'\n')
# Reuse the already checked general joint-wrapper generator, without its unrelated ordinary wrappers.
s=(ROOT/'milestones/48-low-count-compatibility/scripts/wrappers.py').read_text(encoding='utf-8-sig')
s=s[s.index('for case in cases[:2]:'):s.index("s='''import CycleExclusion483")]
exec(compile(s,'joint_wrapper_template','exec'),dict(HERE=HERE,ROOT=ROOT,cases=[case]))
