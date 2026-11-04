"""Record the scope and exact evidence of the completed scaled experiment."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,struct
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
run=H/'data/scaled-floor17';j=read(run/'result.json');s=read(run/'run-status.json')
assert j['status']==s['status']=='PASS_MINIMUM_SCALED_RANGE_AT_MEAN4462'
assert s['exit_code']==0 and s['stop_reason'] is None
assert s['result_sha256']==sha(run/'result.json')
assert j['scaled_mean']==4462 and j['scale']==9 and j['mean']=='4462/9'
assert j['potential_range']==j['certified_range_lower_bound']==5411
assert j['all_edge_inequalities_checked']==4661572 and j['minimum_slack']==0
assert j['target_met'] and not j['target_refuted_at_fixed_mean'] and not j['new_global_bound']
assert j['graph']['weight_sha256']=='22497b6436475fbd248e456d87ed9e7eb7ac4cf9d78ef2804704f1ef905024b2'
assert j['graph']['original156_reproduced']
assert j['graph']['original156_potential_scan']['violation_count']==0
p=run/j['potential_file'];raw=gzip.decompress(p.read_bytes())
assert sha(p)==j['potential_archive_sha256']
assert hashlib.sha256(raw).hexdigest()==j['potential_sha256']
assert len(raw)==1601856*8
lo,hi=None,None
for (v,) in struct.iter_unpack('<q',raw):
    lo=v if lo is None else min(lo,v);hi=v if hi is None else max(hi,v)
assert (lo,hi)==(0,5411)
assert len(j['deficit_walk'])==35 and sum(x['weight'] for x in j['deficit_walk'])==16751
assert 35*4462-9*16751==j['deficit_walk_value']==5411
assert Fraction(j['comparison'])==235-Fraction(3,42262)
prep=read(H/'data/preparation_v5.json')
assert sha(H/'data/preparation_v5.json')==j['preparation_sha256']
assert sha(R/prep['plan_path'])==prep['plan_sha256']
for mapping in [prep['script_pins'],prep['input_pins'],j['completion_pins']]:
    for rel,digest in mapping.items():assert sha(R/rel)==digest,rel
for row in j['journal']:assert sha(run/row['path'])==row['sha256']
a=read(H/'review/walk-audit.json')
assert a['status']=='PASS_INDEPENDENT_SCALED_WALK_AUDIT'
assert (a['walk_length'],a['walk_weight'],a['scaled_deficit'])==(35,16751,5411)
for rel,digest in a['input_sha256'].items():assert sha(R/rel)==digest,rel
assert sha(H/'review/walk-audit.py')==a['audit_script_sha256']
paths=['data/scaled-floor17/result.json','data/scaled-floor17/run-status.json',
       'data/scaled-floor17/potential.i64.gz','data/preparation_v5.json',
       'review/walk-audit.py','review/walk-audit.json','MATHEMATICAL_NOTE.md','scripts/complete.py']
out=dict(status='PASS_CONDITIONAL_SCALED_POTENTIAL_AND_MINIMUM_RANGE',
    evidence_sha256={p:sha(H/p) for p in paths},retained_edges=4661572,
    mean='4462/9',range='5411/9',fixed_mean_minimal=True,
    witness_length=35,witness_weight=16751,rounding_loss_assumed=4,
    conditional_comparison='9931567/42262',gap_below235='3/42262',
    loss_lower_bound_proved=False,inherited_snake_premises_unresolved=True,
    native_all_edge_scan=True,complete_Lean_graph_certificate=False,
    joint_slope_range_optimality=False,new_global_bound=False,
    numerical_Lean_check_pending_milestone=165)
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'])
