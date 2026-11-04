"""Audit the conditional arithmetic and preserve its unresolved hypotheses."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]

def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def main():
    ep=H/'data/remainder-execution-v2.json';plan=read(ep)
    rp=H/'data/RemainderComparison163V2-audit.json';q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    for field,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(q[field])==q[key]
    assert q['source_sha256']==plan['source_sha256']['RemainderComparison163V2']
    for p,d in q['dependencies'].items():assert sha(p)==d,p
    expected=['exact_budget','retained_comparison','saved_witness_equalities',
              'integer_loss_threshold','loss_three_and_four','conditional_edge_bound','aggregate_rounding_example']
    assert sorted(r['theorem'] for r in q['axioms'])==sorted('Snake9.RemainderComparison163.'+x for x in expected)
    assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in q['axioms'])
    result=dict(status='PASS_RETAINED_CORNER_LOSS_ARITHMETIC',execution_plan_sha256=sha(ep),
        receipt_sha256=sha(rp),theorem_reports=q['axioms'],source_sha256=q['source_sha256'],
        statements=7,positive_loss_bound_proved=False,new_full_graph_potential_proved=False,
        actual_share18_theorem_complete=False,new_unconditional_bound=False,
        scope='Retained-loss comparison; exact fixed-parameter threshold4; conditional edge bound234 with packing, budget, potential and loss hypotheses; arithmetic counterexample to rounding faces separately.',
        auditor_sha256=sha(Path(__file__)))
    target=H/'data/remainder-completion.json';assert not target.exists()
    target.write_bytes((json.dumps(result,indent=2)+'\n').encode())
    print(json.dumps({k:v for k,v in result.items() if k!='theorem_reports'},indent=2))

if __name__=='__main__':main()
