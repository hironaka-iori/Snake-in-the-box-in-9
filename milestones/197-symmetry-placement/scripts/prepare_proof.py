from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
module=sys.argv[1] if len(sys.argv)>1 else 'NormalForm197';P=R/'milestones/188-dimensional-constructions'
audit=json.loads((P/'data/LayerJoining-audit.json').read_text())
assert audit['status']=='PASS'
pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py')}
for p,d in audit['dependencies'].items():
    assert sha(p)==d,p
    pins[p]=d
for p in [P/'data/LayerJoining-audit.json',P/'build/LayerJoining.olean']:
    pins[str(p)]=sha(p)
assert sha(audit['source'])==audit['source_sha256']
assert sha(audit['object'])==audit['olean_sha256']
assert sha(audit['log'])==audit['log_sha256']
dependencies=[]
if module.startswith('Neighbours197_'): dependencies=['NormalForm197']
for dep in dependencies:
    receipt=H/'data'/(dep+'-audit.json'); d=json.loads(receipt.read_bytes()); assert d['status']=='PASS'
    pins[str(receipt)]=sha(receipt); pins[str(H/'build'/(dep+'.olean'))]=sha(H/'build'/(dep+'.olean'))
    pins[str(H/'lean'/(dep+'.lean'))]=sha(H/'lean'/(dep+'.lean'))
plan=dict(new_module_order=[module],source_sha256={m:sha(H/'lean'/(m+'.lean')) for m in dependencies+[module]},
    input_pins=pins,lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',
    search_paths=[str(H/'build'),str(P/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
target=H/'data'/(module+'-execution.json')
assert not (H/'data'/(module+'-audit.json')).exists()
target.write_text(json.dumps(plan,indent=2)+'\n')
print('PREPARED',module)
