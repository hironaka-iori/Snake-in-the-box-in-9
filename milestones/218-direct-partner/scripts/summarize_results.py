"""Summarize terminal research queries without turning UNKNOWN into exclusion."""
from pathlib import Path
import hashlib, json
H = Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (H/'data/partner-search.lock').exists()
rows = []
for root in [0,78]:
    F = H/'data/threads1'/('root-'+str(root))
    e = json.loads((F/'execution.json').read_bytes())
    assert e['status'] == 'ACCEPTED_NATIVE_RESULT' and e['exit_code'] == 0 and e['stop_reason'] is None
    r = json.loads((F/'result.json').read_bytes())
    assert e['result_sha256'] == sha(F/'result.json')
    assert r['status'] in ['UNKNOWN','INFEASIBLE','FEASIBLE']
    assert r['status'] != 'FEASIBLE', 'Validate and Lean-check the new192-edge witness before routine publication.'
    rows.append({'root':root, 'status':r['status'], 'elapsed_seconds':r['elapsed_seconds'],
        'solver_seconds':sum(s['solver_seconds'] for s in r['iterations']),
        'branches':sum(s['branches'] for s in r['iterations']), 'conflicts':sum(s['conflicts'] for s in r['iterations']),
        'iterations':len(r['iterations']), 'initial_cycle_cuts':r['initial_cycle_cut_count'],
        'dynamic_cycle_cuts':len(r['dynamic_cycle_cuts']),
        'result_sha256':sha(F/'result.json'), 'receipt_sha256':sha(F/'execution.json'),
        'maximum_sampled_private_bytes':max(s['private_bytes'] for s in e['resource_samples'] if s['private_bytes'] is not None)})
out = {'roots':rows, 'new_q9_record':False, 'new_global_bound':False,
       'both_native_excluded':all(r['status']=='INFEASIBLE' for r in rows),
       'scope':'Two arbitrary93-edge partner queries for one fixed98-edge parent. Native exclusions, if any, have no Lean contradiction certificate. UNKNOWN gives no exclusion.'}
(H/'data/search-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
