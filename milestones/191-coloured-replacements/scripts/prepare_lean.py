from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements';P=R/'milestones/190-exchange-constraints';D=Path(__file__).parent
names=['AttachmentBalance191','AlternatingCounts191']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name in names:(H/'lean'/(name+'.lean')).write_bytes((D/(name+'.lean')).read_bytes())
base=json.loads((P/'data/ExchangeAccounting190-execution.json').read_text());base['new_module_order']=names;base['source_sha256']={n:sha(H/'lean'/(n+'.lean')) for n in names};base['checker_sha256']=sha(H/'scripts/check_core.py');base['search_paths']=[str(H/'build')];base['input_pins']={str(p):sha(p) for p in [H/'data/middle95.json',H/'scripts/native_resources.py']}
for name in names:(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(names,indent=2)+'\n');(H/'scripts/prepare_lean.py').write_bytes(Path(__file__).read_bytes())
