"""Verify a bounded original-clause-to-checkpoint theorem and its dependencies."""
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
    ep=H/'data/prefix-execution.json';plan=read(ep)
    rp=H/'data/Prefix162-audit.json';q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    for field,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(q[field])==q[key]
    assert q['source_sha256']==plan['source_sha256']['Prefix162']
    for p,d in q['dependencies'].items():assert sha(p)==d,p
    assert len(q['axioms'])==1
    report=q['axioms'][0]
    assert report['theorem']=='Snake9.ReplayPrefix162.checked_prefix_true'
    assert set(report['axioms'])<={'propext','Classical.choice','Quot.sound'}
    assert sha(plan['progress_receipt'])==plan['progress_receipt_sha256']
    result=dict(status='PASS_BOUNDED_PREFIX_COMPOSITION',execution_plan_sha256=sha(ep),
        receipt_sha256=sha(rp),progress_receipt=plan['progress_receipt'],
        progress_receipt_sha256=plan['progress_receipt_sha256'],
        theorem=report['theorem'],axioms=report['axioms'],
        completed_groups=plan['completed_groups'],completed_segments=plan['completed_segments'],
        total_checked_deductions=plan['total_checked_deductions'],
        total_checked_references=plan['total_checked_references'],
        remaining_deductions=plan['remaining_deductions'],remaining_references=plan['remaining_references'],
        original_CNF_implies_prefix_checkpoint_truth=True,
        full_share18_replay_complete=False,actual_share18_theorem_complete=False,new_global_bound=False,
        scope='The original clause set implies truth of the checkpoint after the indicated consecutive replay groups. No final empty clause or actual-snake share theorem is proved.',
        auditor_sha256=sha(Path(__file__)))
    out=H/'data/completion.json';payload=(json.dumps(result,indent=2)+'\n').encode()
    assert not out.exists();out.write_bytes(payload)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
