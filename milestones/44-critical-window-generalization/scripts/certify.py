"""Reuse the checked multi-centre counter generator for a new pair inequality."""
from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('joint_certificate',ROOT/'milestones/41-joint-intervening-sum/scripts/certify.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
p.HERE=HERE;p.old.HERE=HERE
p.DIRS=[0,1,2,3,4,0,3,1]
p.BOUNDS=[(0,21)]*7
source=HERE/'data/full-phase2-sum-6.json'
p.build(441,[2,6],6,str(source))
meta=HERE/'data/sum441.json';data=json.loads(meta.read_text())
data['source_probe']='data/full-phase2-sum-6.json'
data['meaning']='For directions (a,b,c,d,e,a,d,b), alpha at offsets 2 and 6 has sum at least 7.'
meta.write_text(json.dumps(data,indent=2)+'\n')
