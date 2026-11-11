from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';P=R/'milestones/188-dimensional-constructions';D=Path('D:/Codex/2026-10-13/new-chat/work')
order=['LayerJoining','TwoCrossings188','ReplacementBudget189','NestedReplacement189']
for n in order:
    src=(P/'lean' if n in order[:2] else D)/(n+'.lean');(H/'lean'/(n+'.lean')).write_bytes(src.read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((P/'data/PortParity188-execution.json').read_text());base['new_module_order']=order;base['source_sha256']={n:sha(H/'lean'/(n+'.lean')) for n in order};base['checker_sha256']=sha(H/'scripts/check_core.py');base['search_paths']=[str(H/'build')];base['input_pins']={str(p):sha(p) for p in [H/'data/replacement-contexts.json',H/'data/known97-replacements.json',H/'scripts/native_resources.py']}
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n');(H/'scripts/prepare_lean.py').write_bytes(Path(__file__).read_bytes())
