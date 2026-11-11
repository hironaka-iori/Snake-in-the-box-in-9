from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
name='TwoCrossings188';assert not (H/'data'/(name+'-audit.json')).exists()
(H/'lean'/(name+'.lean')).write_bytes(Path('D:/Codex/2026-10-13/new-chat/work/TwoCrossings188.lean').read_bytes())
digest=hashlib.sha256((H/'lean'/(name+'.lean')).read_bytes()).hexdigest()
for n in json.loads((H/'data/current-order.json').read_text()):
    if (H/'data'/(n+'-audit.json')).exists():continue
    p=H/'data'/(n+'-execution.json');j=json.loads(p.read_text());j['source_sha256'][name]=digest;p.write_text(json.dumps(j,indent=2)+'\n')
(H/'scripts/refresh_lean.py').write_bytes(Path(__file__).read_bytes())
