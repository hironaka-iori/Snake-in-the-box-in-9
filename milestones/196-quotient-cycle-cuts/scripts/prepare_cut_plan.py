from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/188-dimensional-constructions'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
module=sys.argv[1];names=['CycleCut196','CycleData196']+[f'ConcreteCycle196_{i}' for i in range(3)]
for name in ['CycleCut196']+([] if module=='CycleData196' else ['CycleData196']):
 d=json.loads((H/'data'/(name+'-audit.json')).read_bytes());assert d['status']=='PASS'
 for p,h in d['dependencies'].items():assert sha(p)==h
plan=dict(new_module_order=[module],source_sha256={name:sha(H/'lean'/(name+'.lean')) for name in names},
 input_pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py'),str(H/'data/cycle-cuts.json'):sha(H/'data/cycle-cuts.json')},
 lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',search_paths=[str(H/'build'),str(P/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
target=H/'data'/(module+'-execution.json');assert not target.exists();target.write_text(json.dumps(plan,indent=2)+'\n')
