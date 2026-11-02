"""Copy three exact small semantic sources for fresh support checks."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
folders={'JointCountBridge':'31-joint-counter-soundness','JointCountTags':'31-joint-counter-soundness',
    'MultiCentreCount':'41-joint-intervening-sum'}
copied={}
for name,folder in folders.items():
    source=ROOT/'milestones'/folder/'lean'/f'{name}.lean'
    dest=HERE/'lean'/f'{name}.lean';dest.write_bytes(source.read_bytes())
    copied[name]=dict(origin=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        scope='Exact source copied for a new Lean check')
(HERE/'data/copied-joint-sources.json').write_text(json.dumps(copied,indent=2)+'\n')
print('Copied three small joint-count sources without modification')
