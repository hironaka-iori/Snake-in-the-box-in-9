"""Adapt the completed ordinary-window certificate pipeline to four new keys."""
from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1]
for d in ['lean','data','logs','certificates']:(H/d).mkdir(exist_ok=True)
s=(R/'milestones/29-overlapping-share-windows/scripts/certify.py').read_text(encoding='utf-8')
s=s.replace('from joint import ROOT,HERE,TaggedEncoding,window,candidates',
    "HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]\nsys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))\nfrom joint import TaggedEncoding,window,candidates")
s=s.replace("name=f'joint{i}';mod=f'JointFour{i}'", "name=f'coarse{i}';mod=f'CoarseCount{i}'")
s=s.replace("enc=TaggedEncoding(window(case['dirs']),[(4,4)]*7,radius=4)", "bounds=case['bounds']\n    enc=TaggedEncoding(window(case['dirs']),bounds,radius=4)")
s=s.replace("','.join('(4,4)' for _ in range(7))", "','.join(f'({lo},{hi})' for lo,hi in bounds)")
s=s.replace('bounds=[[4,4]]*7','bounds=bounds')
s=s.replace('for i in [3,0,2,1]:', """for i,case in enumerate(cases):
        phase=[[3,3,6,3,3,6,3],[3,6,3,3,6,3,3],[6,3,3,6,3,3,6],[6,3,3,6,3,3,6]][i]
        case['bounds']=[(x,21 if i<2 and x==6 else x) for x in phase]
    (HERE/'data/cases.json').write_text(json.dumps(cases,indent=2)+'\\n')
    for i in [0,1,3,2]:""")
(H/'scripts/certify.py').write_text(s,encoding='utf-8')
