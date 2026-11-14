"""Start a new local ledger, linking the immutable predecessor by hashes.

Version2 counters and receipt paths are local to this milestone. The history
parent stores the cumulative baseline; previous evidence stays in its original
published milestone rather than being copied into every later round.
"""
from pathlib import Path
import hashlib,json
from joint_continue import engine_pins,encoded
H=Path(__file__).resolve().parents[1];P=H.parent/'215-word-partner-capacity'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=P/'data/case-22';new=H/'data/case-22'
assert not new.exists()
before=(old/'state.json').read_bytes();source=json.loads(before)
assert sha(old/'state.json')=='1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb'
assert source['status']=='OPEN' and source['committed_jobs']==740 and len(source['frontier'])==5
assert len(source['receipts'])==740
for name,digest in source['engine_pins'].items():assert sha(P/name)==digest
for name,digest in source['model_pins'].items():assert sha(old/name)==digest
proofs={}
for name in ['TwoStep216','Joint216','PathJoint216']:
    path=H/'data'/(name+'-audit.json');d=json.loads(path.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    assert sha(d['source'])==d['source_sha256'] and sha(d['object'])==d['olean_sha256']
    for path2,digest in d['dependencies'].items():assert sha(path2)==digest
    proofs[name]=sha(path)
review=H/'logs/joint-engine-review.md';assert review.exists()
history={'milestone':str(P),'state':'data/case-22/state.json','state_sha256':sha(old/'state.json'),
    'publication_commit':'670d633bca81e3efff8d8ba5db0a1ba7079af137',
    'publication_manifest_sha256':sha(P/'data/publication-manifest.json'),
    'chain_audit_sha256':sha(P/'data/chain-audit.json'),
    'cumulative_jobs':source['committed_jobs'],'cumulative_nodes':source['nodes'],
    'cumulative_seconds':source['seconds']}
new.mkdir()
for name in source['model_pins']:(new/name).write_bytes((old/name).read_bytes())
(new/'source-state.json').write_bytes(before)
after=json.loads(before)
after.update(version=2,engine_pins=engine_pins(),committed_jobs=0,nodes=0,seconds=0.0,
    receipts=[],history_parent=history,counter_scope='milestone-local',
    transfer_record='data/frontier-transfer.json')
unchanged=['frontier','next_id','model_pins','status','index']
assert all(after[k]==source[k] for k in unchanged)
raw=encoded(after);(new/'state.json').write_bytes(raw);(new/'initial-state.json').write_bytes(raw)
record={'source_milestone':str(P),'source_state_sha256':sha(old/'state.json'),
    'history_parent':history,'copied_model_files':source['model_pins'],
    'frontier_regions':5,'unchanged_fields':unchanged,'counter_scope':'milestone-local',
    'transferred_state_sha256':hashlib.sha256(raw).hexdigest(),
    'old_engine_pins':source['engine_pins'],'new_engine_pins':after['engine_pins'],
    'proof_receipts':proofs,'source_review_sha256':sha(review),
    'argument':'All five unfinished domain vectors and model files are unchanged. Root-only triple projections preserve all fitting assignments; descendant domains are subsets. Each job reloads original relations. Older receipt history is linked at the frozen published predecessor, not duplicated.',
    'certification_limit':'Native table interpretation, arbitrary-input normalization, C execution and complete traversal retain separate proof obligations.'}
(H/'data/frontier-transfer.json').write_bytes(encoded(record))
assert (old/'state.json').read_bytes()==before
print('TRANSFERRED_FIVE_REGIONS; NEW_LOCAL_LEDGER; SOURCE740_JOBS_LINKED',flush=True)
