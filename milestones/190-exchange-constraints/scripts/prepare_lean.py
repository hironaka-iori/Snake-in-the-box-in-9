from pathlib import Path
import json,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';P=R/'milestones/189-middle-replacements';D=Path('D:/Codex/2026-10-13/new-chat/work');name='ExchangeAccounting190'
(H/'lean'/(name+'.lean')).write_bytes((D/(name+'.lean')).read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((P/'data/ReplacementBudget189-execution.json').read_text());base['new_module_order']=[name];base['source_sha256']={name:sha(H/'lean'/(name+'.lean'))};base['checker_sha256']=sha(H/'scripts/check_core.py');base['search_paths']=[str(H/'build')];base['input_pins']={str(p):sha(p) for p in [H/'data/middle95.json',H/'scripts/native_resources.py']}
(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n');(H/'data/current-order.json').write_text(json.dumps([name],indent=2)+'\n');(H/'scripts/prepare_lean.py').write_bytes(Path(__file__).read_bytes())
