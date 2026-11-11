from pathlib import Path
import hashlib,json
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
changed={}
for p in (H/'lean').glob('CubeRows*.lean'):
    assert not (H/'data'/(p.stem+'-audit.json')).exists()
    p.write_text(p.read_text().replace(':= by decide +kernel',':= by\n  unfold Row\n  decide +kernel'),encoding='utf-8',newline='\n')
    changed[p.stem]=hashlib.sha256(p.read_bytes()).hexdigest()
for n in json.loads((H/'data/current-order.json').read_text()):
    if (H/'data'/(n+'-audit.json')).exists():continue
    p=H/'data'/(n+'-execution.json');j=json.loads(p.read_text());j['source_sha256'].update(changed);p.write_text(json.dumps(j,indent=2)+'\n')
(H/'scripts/unfold_rows.py').write_bytes(Path(__file__).read_bytes())
