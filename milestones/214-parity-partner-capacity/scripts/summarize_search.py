"""Record the completed saved continuation and its exact evidence."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not (H/'data/history-search.lock').exists()
p=H/'data/case-22/state.json';s=json.loads(p.read_bytes())
t=json.loads((H/'data/frontier-transfer.json').read_bytes())
for name,h in s['engine_pins'].items():assert sha(H/name)==h
for name,h in s['model_pins'].items():assert sha(p.parent/name)==h
keys=['nodes','seconds','support_calls','support_removals','support_failures','saturated_budgets','partner_match_calls','partner_subset_failures','partner_tight_sets','partner_tight_removals']
totals={k:0 for k in keys};statuses={};receipts=[]
for name in s['receipts'][t['source_jobs']:]:
    rpath=H/name;r=json.loads(rpath.read_bytes());o=json.loads(rpath.with_name('stdout.json').read_bytes())
    assert r['status']=='ACCEPTED_TRANSITION' and r['exit_code']==0 and not r['hard_stop']
    assert sha(rpath.with_name('stdout.json'))==r['stdout_sha256']
    statuses[o['status']]=statuses.get(o['status'],0)+1
    for k in keys:totals[k]+=o[k]
    receipts.append({'receipt':name,'sha256':sha(rpath),'stop_reason':r['stop_reason']})
assert s['nodes']==t['source_nodes']+totals['nodes']
assert s['committed_jobs']==t['source_jobs']+len(receipts)
summary={'status':s['status'],'jobs':s['committed_jobs'],'new_jobs':len(receipts),'pending':len(s['frontier']),'nodes':s['nodes'],'seconds':s['seconds'],'state_sha256':sha(p),'new_statuses':statuses,'new_operation_totals':totals,'new_receipts':receipts,'scope':'Recorded native operations and saved transitions; repeated removals are not distinct globally excluded assignments. No controlled speed comparison or kernel-certified traversal.'}
(H/'data/search-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='new_receipts'},indent=2))
