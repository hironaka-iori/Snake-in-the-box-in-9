"""Summarize this milestone's local ledger and its linked cumulative baseline."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not (H/'data/history-search.lock').exists()
p=H/'data/case-22/state.json';s=json.loads(p.read_bytes())
assert s['version']==2 and s['counter_scope']=='milestone-local'
parent=s['history_parent'];P=Path(parent['milestone'])
assert sha(P/parent['state'])==parent['state_sha256']
for name,digest in s['engine_pins'].items():assert sha(H/name)==digest
for name,digest in s['model_pins'].items():assert sha(p.parent/name)==digest
keys=['nodes','seconds','support_calls','support_removals','support_failures','saturated_budgets',
      'partner_match_calls','partner_subset_failures','partner_tight_sets','partner_tight_removals',
      'word_match_calls','word_subset_failures','word_tight_sets','word_subset_removals',
      'joint_pair_removals','joint_triples','joint_sweeps','joint_new_relations']
totals={k:0 for k in keys};statuses={};receipts=[]
for name in s['receipts']:
    path=H/name;r=json.loads(path.read_bytes());o=json.loads(path.with_name('stdout.json').read_bytes())
    assert r['status']=='ACCEPTED_TRANSITION' and r['exit_code']==0 and not r['hard_stop']
    assert sha(path.with_name('stdout.json'))==r['stdout_sha256']
    statuses[o['status']]=statuses.get(o['status'],0)+1
    for k in keys:totals[k]+=o[k]
    receipts.append({'receipt':name,'sha256':sha(path),'stop_reason':r['stop_reason']})
assert s['nodes']==totals['nodes'] and s['committed_jobs']==len(receipts)
assert s['seconds']==totals['seconds']
summary={'status':s['status'],'jobs':parent['cumulative_jobs']+s['committed_jobs'],
    'new_jobs':s['committed_jobs'],'pending':len(s['frontier']),
    'nodes':parent['cumulative_nodes']+s['nodes'],'seconds':parent['cumulative_seconds']+s['seconds'],
    'local_nodes':s['nodes'],'local_seconds':s['seconds'],'history_parent':parent,
    'state_sha256':sha(p),'new_statuses':statuses,'new_operation_totals':totals,'new_receipts':receipts,
    'scope':'Version2 ledger is local to this milestone; cumulative totals add the pinned predecessor baseline. Operation counts may repeat across jobs. No controlled speed comparison or kernel-certified traversal.'}
(H/'data/search-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['new_receipts','history_parent']},indent=2))
