from pathlib import Path
import json,hashlib,sys
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation');P=H.parent/'185-critical-kernel'
sys.path.insert(0,str(H/'scripts'));from replan import read
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={};copies=[]
for n in read(P/'data/completion.json')['accepted_module_names']:
 if not n.startswith('Share185.'):continue
 j=read(P/'data'/(n+'-audit.json'));src=Path(j['object']);assert sha(src)==j['olean_sha256']
 dst=H/'build'/(n.replace('.','/')+'.olean');assert not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());assert sha(dst)==j['olean_sha256']
 pins[str(dst)]=j['olean_sha256'];copies.append(dict(module=n,source=str(src),copy=str(dst),sha256=j['olean_sha256']))
for n in read(H/'data/current-order.json'):
 if (H/'data'/(n+'-audit.json')).exists():continue
 p=H/'data'/(n+'-execution.json');j=read(p);j['input_pins'].update(pins);p.write_text(json.dumps(j,indent=2)+'\n')
(H/'data/import-copies.json').write_text(json.dumps({'reason':'Lean resolves an existing Share185 directory in the first search root. Exact accepted package objects must be available together in that root.','copies':copies},indent=2)+'\n')
(H/'scripts/pin_imports.py').write_bytes(Path(__file__).read_bytes());print('copied and pinned',len(copies),'accepted import objects')
