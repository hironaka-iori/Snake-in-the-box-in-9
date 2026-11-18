from pathlib import Path
import hashlib,json,sys,re
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
module=sys.argv[1];pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py')};sources={module:sha(H/'lean'/(module+'.lean'))}
for dep in re.findall(r'^import (\w+)$',(H/'lean'/(module+'.lean')).read_text(encoding='utf-8'),re.M):
 if dep=='Std':continue
 receipt=H/'data'/(dep+'-audit.json');d=json.loads(receipt.read_bytes());assert d['status']=='PASS';pins[str(receipt)]=sha(receipt)
 for p,v in d['dependencies'].items():assert sha(p)==v;pins[p]=v
 for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
  p=d[pk];assert sha(p)==d[hk];pins[p]=sha(p)
 sources[dep]=sha(H/'lean'/(dep+'.lean'))
plan=dict(new_module_order=[module],source_sha256=sources,input_pins=pins,lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',search_paths=[str(H/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
assert not (H/'data'/(module+'-audit.json')).exists()
(H/'data'/(module+'-execution.json')).write_text(json.dumps(plan,indent=2)+'\n');print('PREPARED',module)
