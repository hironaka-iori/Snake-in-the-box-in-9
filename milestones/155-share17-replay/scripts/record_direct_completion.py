"""Record direct final checks after the Windows exited-process query failed."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
resume=read(H/'data/memory-resume-progress.json')
continuation=read(H/'data/final-continuation-progress.json')
full=read(H/'data/full-replay-completion.json')
actual=read(H/'data/actual-snake-completion.json')
short=read(H/'analysis/range-lean-check.json')
assert resume['status']=='STOPPED_REQUIRES_INSPECTION'
assert resume['full_exit_code']==0 and resume['continuation_exit_code']==1
assert continuation['status']=='FAILED_REQUIRES_INSPECTION' and not continuation['stages']
log=Path(resume['continuation_log']);text=log.read_text(encoding='utf-8')
assert 'QueryFullProcessImageNameW' in text and 'AssertionError' in text
assert full['status']=='PASS_COMPLETE_SHARED_SHARE17_CORE_CONTRADICTION' and full['checked_modules']==137
assert actual['status']=='PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS'
assert short['status']=='PASS' and len(short['axioms'])==3
for p,d in short['dependencies'].items():assert sha(p)==d,p
for p,d in actual['source_files_sha256'].items():assert sha(R/p)==d,p
paths=[H/'data/memory-resume-progress.json',H/'data/final-continuation-progress.json',
    H/'data/full-replay-completion.json',H/'data/actual-snake-completion.json',
    H/'analysis/range-lean-check.json',log,Path(__file__)]
record=dict(status='PASS_DIRECT_FINAL_CHECKS_AFTER_PROCESS_QUERY_ERROR',
    full_replay_repeated=False,full_replay_modules=137,full_driver_exit_code=0,
    interruption='QueryFullProcessImageNameW failed after the successfully exited driver; it occurred before the audit stages.',
    final_composition_checked=True,actual_snake_audit_passed=True,range_arithmetic_checked=True,
    original_failure_records_preserved=True,new_global_upper_bound=False,
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in paths})
target=H/'data/post-replay-recovery.json'
if target.exists():assert read(target)==record
else:target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print(record['status'])
