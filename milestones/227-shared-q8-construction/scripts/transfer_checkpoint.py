"""Move only a clean time-limit frontier to the atomic-update worker."""
from pathlib import Path
import copy,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
old=H/'data/shared120/checkpoint.json';r=read(H/'data/shared120-execution.json')
assert r['status']=='ACCEPTED_NATIVE_RESULT' and r['exit_code']==0 and r['stop_reason'] is None
assert all(sha(p)==h for p,h in r['pins'].items())
assert sha(H/'data/shared120/result.json')==r['result_sha256']
assert read(H/'data/shared120/result.json')['checkpoint_sha256']==sha(old)
j=read(old);assert j['status']=='TIME_LIMIT'
assert j['pins']['script_sha256']==sha(H/'scripts/shared_paths.py')
changed=copy.deepcopy(j);changed['pins']['script_sha256']=sha(H/'scripts/shared_paths_atomic.py')
out=H/'data/shared120-atomic-checkpoint.json';assert not out.exists();save(out,changed)
restored=read(out);restored['pins']['script_sha256']=j['pins']['script_sha256'];assert restored==j
save(H/'data/checkpoint-transfer.json',dict(status='EXACT_STATE_TRANSFER',source=str(old),source_sha256=sha(old),destination=str(out),destination_sha256=sha(out),original_worker_sha256=j['pins']['script_sha256'],new_worker_sha256=changed['pins']['script_sha256'],only_changed_field='pins.script_sha256',execution_receipt_sha256=sha(H/'data/shared120-execution.json'),scope='The initial worker is safe for this ordinary top-of-loop TIME_LIMIT state. Its asynchronously interrupted frontier is not accepted. The successor uses single state assignments; search rules are unchanged.'))
print('TRANSFERRED_EXACT_TIME_LIMIT_STATE',len(j['state']['first_frontier']))
