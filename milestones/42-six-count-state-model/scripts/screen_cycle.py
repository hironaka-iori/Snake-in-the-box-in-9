"""Test the certified graph cycle in the stronger seven-centre geometric model."""
from pathlib import Path
import hashlib,importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('prior_probe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE
source=HERE/'data/analysis.json';a=json.loads(source.read_text());assert a['potential_verified']
for i,row in enumerate(a['cycle']):
 p.DIRS=row['directions'];p.solve('screen-'+str(i),row['counts'],seconds=8)
(HERE/'data/screen-source.json').write_text(json.dumps(dict(analysis_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),model='Radius-four acyclic local model with seven count upper bounds',scope='Solver evidence only; no new exclusion theorem.'),indent=2)+'\n')
