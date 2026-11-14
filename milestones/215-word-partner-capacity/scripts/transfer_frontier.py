"""Preserve the complete round214 record while changing only engine pins."""
from pathlib import Path
import hashlib,json,shutil
from word_continue import engine_pins,encoded
H=Path(__file__).resolve().parents[1];P=H.parent/'214-parity-partner-capacity'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=P/'data/case-22';new=H/'data/case-22'
assert not new.exists()
before=(old/'state.json').read_bytes();state=json.loads(before)
assert sha(old/'state.json')=='eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027'
assert state['status']=='OPEN' and state['committed_jobs']==240 and len(state['frontier'])==13
for name,h in state['engine_pins'].items():assert sha(P/name)==h
for name,h in state['model_pins'].items():assert sha(old/name)==h
proof=json.loads((H/'data/PathWordCapacity215-audit.json').read_bytes())
assert proof['status']=='PASS' and proof['exit_code']==0 and proof['stop_reason'] is None
assert sha(proof['source'])==proof['source_sha256'] and sha(proof['object'])==proof['olean_sha256']
for name,h in proof['dependencies'].items():assert sha(name)==h
assert (H/'logs/word-engine-review.md').exists()
shutil.copytree(old,new)
copied={str(p.relative_to(old)):sha(p) for p in old.rglob('*') if p.is_file()}
assert all(sha(new/name)==h for name,h in copied.items())
aliases={'state.json':'transfer214-state.json','initial-state.json':'transfer214-initial-state.json'}
for name,alias in aliases.items():
    assert not (new/alias).exists()
    (new/alias).write_bytes((new/name).read_bytes())
after=json.loads(before);after['engine_pins']=engine_pins();after['transfer_record']='data/frontier-transfer.json'
raw=encoded(after);(new/'state.json').write_bytes(raw);(new/'initial-state.json').write_bytes(raw)
unchanged=['frontier','next_id','committed_jobs','nodes','seconds','receipts','model_pins','status','index','version']
assert all(after[k]==state[k] for k in unchanged)
record={'source_milestone':str(P),'source_state_sha256':hashlib.sha256(before).hexdigest(),'source_files_sha256':copied,'source_file_aliases':aliases,'source_jobs':240,'source_nodes':state['nodes'],'source_seconds':state['seconds'],'frontier_regions':13,'unchanged_fields':unchanged,'transferred_state_sha256':hashlib.sha256(raw).hexdigest(),'old_engine_pins':state['engine_pins'],'new_engine_pins':after['engine_pins'],'proof_receipt_sha256':sha(H/'data/PathWordCapacity215-audit.json'),'source_review_sha256':sha(H/'logs/word-engine-review.md'),'argument':'All thirteen unfinished regions and the original model are unchanged. The added rule rejects a distinct-word subset only after a deficient union count, or removes a tight union from other members of the same chosen/outside family. The source-specific path theorem derives the distinctness and conflict premises.','certification_limit':'Native masks, matching discovery, normalization and complete traversal remain separate from the checked path/counting proof.'}
(H/'data/frontier-transfer.json').write_bytes(encoded(record))
assert (old/'state.json').read_bytes()==before
print('TRANSFERRED',len(copied),'files and 13 identical regions',flush=True)
