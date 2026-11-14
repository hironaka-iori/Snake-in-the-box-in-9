"""Transfer unchanged unfinished regions to the tighter partner engine."""
from pathlib import Path
import hashlib,json,shutil
from tight_continue import engine_pins,encoded
H=Path(__file__).resolve().parents[1];P=H.parent/'212-spare-support'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=P/'data/case-22';new=H/'data/case-22'
assert not new.exists()
before=(old/'state.json').read_bytes();state=json.loads(before)
assert sha(old/'state.json')=='6a2090ba3a2af9561461bf7ff5f6ef133996a25c13dbc32d48f74d29b2aa90a8'
assert state['status']=='OPEN' and state['committed_jobs']==120 and len(state['frontier'])==11
for name,h in state['engine_pins'].items():assert sha(P/name)==h
for name,h in state['model_pins'].items():assert sha(old/name)==h
proof=json.loads((H/'data/TightPartner214-audit.json').read_bytes())
assert proof['status']=='PASS' and proof['exit_code']==0 and proof['stop_reason'] is None
assert sha(proof['source'])==proof['source_sha256'] and sha(proof['object'])==proof['olean_sha256']
for name,h in proof['dependencies'].items():assert sha(name)==h
assert (H/'logs/tight-engine-review.md').exists(), 'Independent source review required before transfer.'
shutil.copytree(old,new)
copied={str(p.relative_to(old)):sha(p) for p in old.rglob('*') if p.is_file()}
assert all(sha(new/name)==h for name,h in copied.items())
(new/'source-state.json').write_bytes(before)
(new/'source-initial-state.json').write_bytes((new/'initial-state.json').read_bytes())
after=json.loads(before);after['engine_pins']=engine_pins();after['transfer_record']='data/frontier-transfer.json'
raw=encoded(after)
(new/'state.json').write_bytes(raw);(new/'initial-state.json').write_bytes(raw)
unchanged=['frontier','next_id','committed_jobs','nodes','seconds','receipts','model_pins','status','index','version']
assert all(after[k]==state[k] for k in unchanged)
record={'source_milestone':str(P),'source_state_sha256':hashlib.sha256(before).hexdigest(),'source_files_sha256':copied,'source_jobs':120,'source_nodes':state['nodes'],'source_seconds':state['seconds'],'frontier_regions':11,'unchanged_fields':unchanged,'transferred_state_sha256':hashlib.sha256(raw).hexdigest(),'old_engine_pins':state['engine_pins'],'new_engine_pins':after['engine_pins'],'proof_receipt_sha256':sha(H/'data/TightPartner214-audit.json'),'source_review_sha256':sha(H/'logs/tight-engine-review.md'),'argument':'The complete saved model and eleven unfinished regions are identical. The new engine adds necessary partner-subset rejection and tight-subset support filtering. Candidate subsets are discovered by matching; the actual neighbor cardinality is checked before every use. Matching success is never treated as a valid word assignment.','certification_limit':'Generic deductions pass Lean; the native implementation and whole historical traversal are not kernel-certified.'}
(H/'data/frontier-transfer.json').write_bytes(encoded(record))
assert (old/'state.json').read_bytes()==before
print('TRANSFERRED',len(copied),'files and 11 identical regions')
