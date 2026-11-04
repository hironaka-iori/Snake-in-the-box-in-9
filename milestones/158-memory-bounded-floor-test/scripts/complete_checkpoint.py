"""Verify the accepted finite obstruction and Lean arithmetic evidence."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def pins(mapping):
    for p,d in mapping.items():assert sha(R/p)==d,p

run=H/'data/floor17-complete'
j=read(run/'result.json');s=read(run/'run-status.json')
assert j['status']==s['status']=='PASS_FIXED_MEAN_TARGET_OBSTRUCTION'
assert s['exit_code']==0 and s['stop_reason'] is None
assert s['result_sha256']==sha(run/'result.json')
assert j['deficit_walk_value']==633 and len(j['deficit_walk'])==149
assert sum(e['weight'] for e in j['deficit_walk'])==73271
assert j['potential_file'] is None and not j['target_met'] and j['target_refuted_at_fixed_mean']
assert j['graph']['original156_reproduced'] and j['graph']['original156_potential_scan']['violation_count']==0
assert j['graph']['weight_sha256']=='22497b6436475fbd248e456d87ed9e7eb7ac4cf9d78ef2804704f1ef905024b2'
prep=read(H/'data/preparation_v5.json')
assert sha(H/'data/preparation_v5.json')==j['preparation_sha256']
assert sha(R/prep['plan_path'])==prep['plan_sha256']
for m in [prep['script_pins'],prep['input_pins'],j['completion_pins']]:pins(m)
for row in j['journal']:assert sha(run/row['path'])==row['sha256']
audit=read(H/'review/cycle-audit.json')
assert audit['status']=='PASS_SELECTED_CYCLE_OLD_WALK_AND_FULL149_AUDIT'
pins(audit['input_sha256'])
lean=read(H/'data/floor-lean-check.json')
assert lean['status']=='PASS' and lean['exit_code']==0 and len(lean['axioms'])==6
pins(lean['dependencies'])
for row in lean['axioms']:assert set(row['axioms']) <= {'propext','Classical.choice','Quot.sound'}
assert sha(lean['log'])==lean['log_sha256'] and sha(lean['object'])==lean['olean_sha256']
protected={'.gitignore':'20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b','milestones/50-three-count-return/excess-screen/data/critical-family.json':'466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'}
pins(protected)
evidence=['data/floor17-complete/result.json','data/floor17-complete/run-status.json','data/preparation_v5.json','review/cycle-audit.json','data/floor-lean-check.json','MATHEMATICAL_NOTE.md','scripts/complete_checkpoint.py']
out=dict(status='PASS_WEAKER_FLOOR_OBSTRUCTION_ALL_MEANS_AND_UNIFORM_CREDITS',
    evidence_sha256={p:sha(H/p) for p in evidence},cycle_length=9,cycle_weight=4462,
    cycle_occurrence_events=0,walk_length=9,walk_weight=3861,walk_occurrence_events=0,
    comparison_lower_bound='9931745/42262',comparison_gap_above235='175/42262',
    comparison_attainment_claimed=False,Lean_arithmetic_statements=6,
    complete_Lean_graph_certificate=False,new_global_bound=False,
    source_mask_reused=True,original156_weights_reproduced=True,
    previous_hypothesis_refuted=True,protected_files_sha256=protected,
    paper_last_full_revision=156,paper_next_full_revision=166)
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'])
