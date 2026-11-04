"""Small source-only helpers for161; no compiler or solver invocation."""
from pathlib import Path
import hashlib
import json
import time

H=Path(__file__).resolve().parents[1];R=H.parents[1]
M144=R/'milestones/144-countfree-share18'
M160=R/'milestones/160-share18-replay-transport'


def retry(action):
    for attempt in range(40):
        try:return action()
        except PermissionError:
            if attempt==39:raise
            time.sleep(.05)


def read(path):return retry(lambda:json.loads(Path(path).read_text(encoding='utf-8-sig')))


def sha(path):
    value=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):value.update(block)
    return value.hexdigest()


def save(path,value):
    tmp=path.with_suffix(path.suffix+'.tmp')
    retry(lambda:tmp.write_bytes((json.dumps(value,indent=2)+'\n').encode('utf-8')))
    retry(lambda:tmp.replace(path))


def check_pins(plan):
    for name,digest in {**plan['source_pins'],**plan['input_pins']}.items():
        assert sha(R/name)==digest,name


def completed160():
    completion=read(M160/'data/completion.json')
    assert completion['status']=='PASS_ACCEPTED_PREFIX_CHECKPOINT_TRUTH'
    assert completion['original_CNF_implies_checkpoint_truth']
    assert (completion['prefix_deductions'],completion['prefix_references'])==(1055,6006)
    assert (completion['remaining_replay_deductions'],completion['remaining_replay_references'])==(144160,14704875)
    assert not completion['full_share18_replay_complete'] and not completion['new_global_bound']
    for name,digest in completion['receipt_sha256'].items():
        path=M160/name;assert sha(path)==digest
        receipt=read(path)
        assert receipt['status']=='PASS' and receipt['exit_code']==0 and receipt['stop_reason'] is None
        assert sha(receipt['source'])==receipt['source_sha256']
        assert sha(receipt['object'])==receipt['olean_sha256']
        assert sha(receipt['log'])==receipt['log_sha256']
        assert all(set(row['axioms'])<={'propext','Classical.choice','Quot.sound'} for row in receipt['axioms'])
    assert read(M160/'data/checkpoint-progress.json')['status']=='PASS_COMPLETE_CHECKPOINT_MODULES'
    assert sha(M160/'data/prefix1055/prefix-transport.json')==completion['native_receipt_sha256']
    return completion


def no_batch_locks():
    paths=[M160/'data/checkpoint-batch.lock',M160/'data/prefix-transport.lock',
        R/'milestones/159-share18-proof-continuation/data/semantic-batch.lock',
        R/'milestones/159-share18-proof-continuation/data/semantic-final-batch.lock']
    return not any(path.exists() for path in paths)
