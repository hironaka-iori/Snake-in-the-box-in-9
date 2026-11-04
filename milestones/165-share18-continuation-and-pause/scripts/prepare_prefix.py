"""Prepare a bounded prefix consequence after accepted replay groups."""
from pathlib import Path
import argparse, hashlib, json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/161-share18-full-replay'

def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def write(p,b):
    b=b.encode() if isinstance(b,str) else b
    p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',required=True);a=ap.parse_args()
    rp=Path(a.receipt).resolve();rp.relative_to(P/'data');q=read(rp)
    assert q['status']=='PASS_BOUNDED_REPLAY_GROUPS'
    assert not (P/'data/replay-batch.lock').exists()
    ep=P/'data/kernel-execution.json';assert sha(ep)==q['execution_plan_sha256'];previous=read(ep)
    sp=P/'data/full-source-plan.json';assert sha(sp)==q['source_plan_sha256'];source=read(sp)
    groups=source['groups'][:q['completed_groups']]
    assert groups[-1]['after_segment']==q['completed_group_segments']
    assert groups[-1]['after_step']==q['continuation_deductions_in_completed_groups']
    assert len(groups)<source['full_checkpoint_groups']
    pins=dict(previous['input_pins'])
    def pin(path,value=None):
        path=Path(path).resolve();d=sha(path)
        assert value is None or value==d,str(path)
        pins[str(path)]=d
    for path,value in list(pins.items()):assert sha(path)==value,path
    for path in [rp,ep,sp]:pin(path)
    pin(P/q['progress_record'],q['progress_sha256'])
    pin(P/'scripts/audit_progress.py',q['auditor_sha256'])
    for item in q['receipts'].values():
        path=P/item['path'];pin(path,item['sha256']);row=read(path)
        assert row['status']=='PASS' and row['exit_code']==0 and row['stop_reason'] is None
        for field,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:pin(row[field],row[key])
        for path,value in row['dependencies'].items():
            if path in pins:assert pins[path]==value
            else:pin(path,value)
    target=groups[-1]['after_segment']
    lines=['import CheckpointConsequence160']+[f'import ReplaySteps161_{g["group"]:04d}' for g in groups]
    lines+=['set_option maxHeartbeats 0','set_option Elab.async false',
        'namespace Snake9.ReplayPrefix165','open Snake9.Lrat144 (TreeTrue)','open Snake9.ReplayFull161',
        'theorem checked_prefix_true (τ : Nat → Bool)',
        '    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :',
        f'    TreeTrue τ start{target} := by',
        '  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h']
    for g in groups:
        begin,end=g['first_segment'],g['after_segment']
        lines.append(f'  have h{end} : TreeTrue τ start{end} := steps{g["group"]} τ h{begin}')
    lines += [f'  exact h{target}','#print axioms checked_prefix_true','end Snake9.ReplayPrefix165']
    src=H/'lean/Prefix165.lean';write(src,'\n'.join(lines)+'\n')
    checker=(P/'scripts/check_replay.py').read_text().replace('data/kernel-execution.json','data/prefix-execution.json')
    write(H/'scripts/check_prefix.py',checker)
    write(H/'scripts/native_resources.py',(P/'scripts/native_resources.py').read_bytes())
    for path in [Path(__file__),H/'scripts/check_prefix.py',H/'scripts/native_resources.py']:pin(path)
    plan=dict(status='PREPARED_BOUNDED_PREFIX_CONSEQUENCE',module_order=['Prefix165'],new_module_order=['Prefix165'],
        source_sha256={'Prefix165':sha(src)},input_pins=pins,lean_bin=previous['lean_bin'],
        search_paths=[str(H/'build')]+previous['search_paths'],checker_sha256=sha(H/'scripts/check_prefix.py'),
        progress_receipt=str(rp),progress_receipt_sha256=sha(rp),completed_groups=len(groups),completed_segments=target,
        total_checked_deductions=q['total_deductions_in_completed_groups'],total_checked_references=q['total_references_in_completed_groups'],
        remaining_deductions=q['remaining_deductions'],remaining_references=q['remaining_references'],
        full_share18_replay_complete=False,actual_share18_theorem_complete=False,new_global_bound=False)
    write(H/'data/prefix-execution.json',json.dumps(plan,indent=2)+'\n');write(H/'.gitattributes','* -text\n')
    print('PREPARED_PREFIX_CONSEQUENCE',target,'segments')

if __name__=='__main__':main()
