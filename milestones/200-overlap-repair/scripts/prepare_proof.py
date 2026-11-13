from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
module=sys.argv[1] if len(sys.argv)>1 else 'CollisionRepair200';P=R/'milestones/191-coloured-replacements'
auditpath=P/'data/AttachmentBalance191-audit.json';audit=json.loads(auditpath.read_bytes());assert audit['status']=='PASS'
pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py'),str(auditpath):sha(auditpath)}
for p,d in audit['dependencies'].items():assert sha(p)==d,p;pins[p]=d
for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
 p=audit[pk];assert sha(p)==audit[hk];pins[p]=sha(p)
plan=dict(new_module_order=[module],source_sha256={module:sha(H/'lean'/(module+'.lean'))},input_pins=pins,lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',search_paths=[str(H/'build'),str(P/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
assert not (H/'data'/(module+'-audit.json')).exists()
(H/'data'/(module+'-execution.json')).write_text(json.dumps(plan,indent=2)+'\n');print('PREPARED',module)
