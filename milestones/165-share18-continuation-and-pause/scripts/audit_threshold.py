"""Audit numerical Lean checks and their relation to the separate native graph result."""
from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
p=H/'data/Threshold165-audit.json';q=read(p)
assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
for field,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(q[field])==q[key]
for path,digest in q['dependencies'].items():assert sha(path)==digest,path
names=['scaled_comparison','integer_edge_bound','saved_walks','attained_comparison','conditional_edge_bound']
assert sorted(x['theorem'] for x in q['axioms'])==sorted('Snake9.Threshold165.'+n for n in names)
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
f=R/'milestones/164-loss-corrected-potential/data/completion.json';g=read(f)
assert g['status']=='PASS_CONDITIONAL_SCALED_POTENTIAL_AND_MINIMUM_RANGE'
for path,digest in g['evidence_sha256'].items():assert sha(f.parent.parent/path)==digest,path
assert g['witness_length']==35 and g['witness_weight']==16751 and g['range']=='5411/9'
result=dict(status='PASS_FIVE_NUMERICAL_LEAN_STATEMENTS',receipt_sha256=sha(p),native_completion_sha256=sha(f),axioms=q['axioms'],native_graph_result_separately_verified=True,graph_inequalities_checked_in_Lean=False,rounding_loss_lower_bound_proved=False,new_unconditional_bound=False,auditor_sha256=sha(__file__))
out=H/'data/threshold-completion.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS_FIVE_NUMERICAL_LEAN_STATEMENTS')
