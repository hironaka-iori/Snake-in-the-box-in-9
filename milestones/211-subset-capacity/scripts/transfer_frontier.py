"""Transfer the unchanged covering frontier to a separately justified engine."""
from pathlib import Path
import hashlib,json,shutil
from capacity_continue import engine_pins,encoded
H=Path(__file__).resolve().parents[1]
P=H.parent/'209-slice-capacity'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=P/'data/case-23';new=H/'data/case-23'
if new.exists():raise RuntimeError('Preserve existing destination and transfer record.')
completion=json.loads((P/'data/completion.json').read_bytes())
case=next(x for x in completion['cases'] if x['index']==23)
assert sha(old/'state.json')==case['state_sha256']
before=(old/'state.json').read_bytes();state=json.loads(before)
assert state['status']=='OPEN' and state['committed_jobs']==100 and len(state['frontier'])==7
for name,digest in state['engine_pins'].items():assert sha(P/name)==digest
for name,digest in state['model_pins'].items():assert sha(old/name)==digest
proof=json.loads((H/'data/Subset211-audit.json').read_bytes())
assert proof['status']=='PASS' and proof['exit_code']==0 and proof['stop_reason'] is None
assert sha(Path(proof['source']))==proof['source_sha256']
assert sha(Path(proof['object']))==proof['olean_sha256']
for name,digest in proof['dependencies'].items():assert sha(Path(name))==digest
shutil.copytree(old,new)
copied={str(p.relative_to(old)):sha(p) for p in old.rglob('*') if p.is_file()}
assert all(sha(new/name)==digest for name,digest in copied.items())
(new/'source-state.json').write_bytes(before)
(new/'source-initial-state.json').write_bytes((new/'initial-state.json').read_bytes())
after=json.loads(before);after['engine_pins']=engine_pins()
after['transfer_record']='data/frontier-transfer.json'
raw=encoded(after)
(new/'state.json').write_bytes(raw);(new/'initial-state.json').write_bytes(raw)
record={
 'source_milestone':str(P),'source_state_sha256':sha(old/'state.json'),
 'source_completion_sha256':sha(P/'data/completion.json'),
 'source_files_sha256':copied,'source_jobs':100,'source_nodes':state['nodes'],
 'source_seconds':state['seconds'],'frontier_regions':len(state['frontier']),
 'unchanged_fields':['frontier','next_id','committed_jobs','nodes','seconds','receipts','model_pins','status','index','version'],
 'transferred_state_sha256':hashlib.sha256(raw).hexdigest(),
 'old_engine_pins':state['engine_pins'],'new_engine_pins':after['engine_pins'],
 'proof_receipt_sha256':sha(H/'data/Subset211-audit.json'),
 'argument':'All seven domain vectors and the model are identical. The new engine only removes words from clique variables outside an explicitly counted tight subset, or rejects an explicitly deficient subset. Subset211 checks those finite-list implications; concrete masks and matching discovery retain native scope.',
 'certification_limit':'No claim that Lean certifies the native engine, historical traversal, or complete snake-to-model interpretation.'}
for key in record['unchanged_fields']:assert after[key]==state[key]
(H/'data/frontier-transfer.json').write_bytes(encoded(record))
print('TRANSFERRED',len(copied),'unchanged input/history files;',len(state['frontier']),'identical unfinished domain vectors.')
