"""Add the cycle-hitting conditional rule to the pinned ten-rule experiment."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
rules=read(ROOT/'milestones/115-total-count-certificate/data/universal345-total22/results.json')['rules']
probe=read(HERE/'data/probes/012034-middle5-outer15.json')
assert probe['status']=='UNSAT_UNCERTIFIED'
rule={key:probe[key] for key in ['directions','bounds','positions']}
rule.update(name='012034-middle5-outer16',lower=16,probe=(HERE/'data/probes/012034-middle5-outer15.json').relative_to(ROOT).as_posix())
rules=rules+[rule]
path=HERE/'data/middle5-rules.json';assert not path.exists()
path.write_text(json.dumps(rules,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(rules),'rules; new outer-four lower bound remains a hypothesis.')
