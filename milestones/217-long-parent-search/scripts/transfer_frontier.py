"""Continue a frozen version2 ledger with the identical accepted engine."""
from pathlib import Path
import hashlib,json
from joint_continue import engine_pins,encoded
H=Path(__file__).resolve().parents[1];P=H.parent/'216-joint-word-support'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=P/'data/case-22';new=H/'data/case-22';assert not new.exists()
before=(old/'state.json').read_bytes();source=json.loads(before)
assert sha(old/'state.json')=='4599f3f699d81ee7e14295d537715d621db8a9bb5584ea8a9121d4f2ed592480'
assert source['version']==2 and source['counter_scope']=='milestone-local'
assert source['status']=='OPEN' and source['committed_jobs']==400 and len(source['frontier'])==9
assert len(source['receipts'])==400
summary=json.loads((P/'data/search-summary.json').read_bytes())
assert summary['state_sha256']==sha(old/'state.json')
for total,local in [('jobs','committed_jobs'),('nodes','nodes'),('seconds','seconds')]:
    assert summary[total]==source['history_parent']['cumulative_'+total]+source[local]
assert summary['jobs']==1140 and summary['nodes']==6496107
for name,digest in source['engine_pins'].items():
    assert sha(P/name)==digest==sha(H/name)
for name,digest in source['model_pins'].items():assert sha(old/name)==digest
assert engine_pins()==source['engine_pins']
compiler=json.loads((P/'data/joint-compiler-receipt.json').read_bytes())
assert compiler['exit_code']==0
assert compiler['source_sha256']==sha(H/'scripts/joint_solver.c')
assert compiler['binary_sha256']==sha(H/'build/joint_solver.exe')
refs={str(P/'data/joint-compiler-receipt.json'):sha(P/'data/joint-compiler-receipt.json'),
      str(P/'logs/joint-engine-review.md'):sha(P/'logs/joint-engine-review.md')}
for name in ['TwoStep216','Joint216','PathJoint216','LiteralJoint216']:
    path=P/'data'/(name+'-audit.json');d=json.loads(path.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    assert sha(d['source'])==d['source_sha256'] and sha(d['object'])==d['olean_sha256']
    for path2,digest in d['dependencies'].items():assert sha(path2)==digest
    refs[str(path)]=sha(path)
history={'milestone':str(P),'state':'data/case-22/state.json','state_sha256':sha(old/'state.json'),
    'publication_commit':'cfa2e8ed386259be99cd2564361591cd92a3b7bc',
    'publication_manifest_sha256':sha(P/'data/publication-manifest.json'),
    'chain_audit_sha256':sha(P/'data/chain-audit.json'),
    'search_summary_sha256':sha(P/'data/search-summary.json'),
    'cumulative_jobs':summary['jobs'],'cumulative_nodes':summary['nodes'],
    'cumulative_seconds':summary['seconds']}
new.mkdir()
for name in source['model_pins']:(new/name).write_bytes((old/name).read_bytes())
(new/'source-state.json').write_bytes(before)
after=json.loads(before)
after.update(engine_pins=engine_pins(),committed_jobs=0,nodes=0,seconds=0.0,
    receipts=[],history_parent=history,transfer_record='data/frontier-transfer.json')
unchanged=['frontier','next_id','model_pins','status','index','version','counter_scope']
assert all(after[k]==source[k] for k in unchanged)
raw=encoded(after);(new/'state.json').write_bytes(raw);(new/'initial-state.json').write_bytes(raw)
record={'source_milestone':str(P),'source_state_sha256':sha(old/'state.json'),
    'history_parent':history,'copied_model_files':source['model_pins'],'frontier_regions':9,
    'unchanged_fields':unchanged,'counter_scope':'milestone-local',
    'transferred_state_sha256':hashlib.sha256(raw).hexdigest(),
    'old_engine_pins':source['engine_pins'],'new_engine_pins':after['engine_pins'],
    'reused_evidence':refs,'engine_changed':False,
    'argument':'All nine unfinished vectors, model files, native source, driver and executable are unchanged. Only the ledger baseline is advanced to the pinned cumulative summary. Longer submitted time budgets change neither the mathematical model nor the accepted propagation rules.',
    'certification_limit':'Existing native table interpretation, arbitrary-input normalization, C execution and complete traversal obligations remain.'}
(H/'data/frontier-transfer.json').write_bytes(encoded(record))
assert (old/'state.json').read_bytes()==before
print('TRANSFERRED_NINE_REGIONS; IDENTICAL_ENGINE; CUMULATIVE1140_JOBS_LINKED',flush=True)
