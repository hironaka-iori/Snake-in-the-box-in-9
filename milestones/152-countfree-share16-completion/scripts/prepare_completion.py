"""Prepare a final checker that refuses to run before complete replay audit."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
T=R/'milestones/150-actual-pair-share';P=R/'milestones/151-countfree-replay-pilot'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def change(s,a,b):assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
plan=read(T/'data/semantic-plan.json');source=H/'lean/ShareComplete152.lean'
plan.update(status='PREPARED_FINAL_COMPOSITION_REPLAY_PENDING',module_order=['ShareComplete152'],
    framework_modules=['ShareComplete152'],artifacts=[dict(module='ShareComplete152',path=source.relative_to(H).as_posix(),sha256=sha(source))],
    checked=False,selected_scope='Compile only after all342 replay modules and the complete saved-evidence audit pass.',
    preparer_sha256=sha(Path(__file__)))
out=H/'data/completion-plan.json';assert not out.exists();out.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
old=T/'scripts/check_module.py';s=old.read_text(encoding='utf-8').replace('data/semantic-plan.json','data/completion-plan.json')
needle="read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))\n"
guard="""P=R/'milestones/151-countfree-replay-pilot';T=R/'milestones/150-actual-pair-share';U=R/'milestones/148-actual-snake-share-transfer'
progress=read(P/'data/full-replay-progress.json')
if progress['status']!='PASS_COMPLETE_FULL_REPLAY_MODULES' or progress['active'] is not None:
    print(json.dumps(dict(status='WAITING_FOR_COMPLETE_REPLAY',replay_status=progress['status'],checked=len(progress['checked_modules']))))
    raise SystemExit(2)
assert len(progress['checked_modules'])==342 and not (P/'data/full-replay-batch.lock').exists()
complete=read(H/'data/replay-completion.json')
assert complete['status']=='PASS_COMPLETE_012032_CORE_CONTRADICTION' and complete['checked_modules']==342
assert hashlib.sha256((P/'data/full-execution-plan.json').read_bytes()).hexdigest()==complete['full_execution_plan_sha256']
assert hashlib.sha256((P/'data/ReplayUnsat150-audit.json').read_bytes()).hexdigest()==complete['final_unsat_receipt_sha256']
"""
s=change(s,needle,needle+guard)
s=change(s,"[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build']+external", "[build,P/'build',T/'build',U/'build',Q/'build']+external")
s=change(s,"    if not rp.exists():rp=R/'milestones/148-actual-snake-share-transfer/data'/(name+'-audit.json')",
    "    if not rp.exists():rp=P/'data'/(name+'-audit.json')\n    if not rp.exists():rp=T/'data'/(name+'-audit.json')\n    if not rp.exists():rp=U/'data'/(name+'-audit.json')")
s=change(s,"[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build',B.parent/'lib/lean']+external",
    "[build,P/'build',T/'build',U/'build',Q/'build',B.parent/'lib/lean']+external")
s=change(s,"paths=[str(build),str(Q/'build')]+list(map(str,external))",
    "paths=[str(build),str(P/'build'),str(T/'build'),str(U/'build'),str(Q/'build')]+list(map(str,external))")
s=change(s,"    for p,d in q['dependencies'].items():\n        assert sha(p)==d,p;deps[p]=d",
    "    for p,d in q['dependencies'].items():\n        if p in deps:assert deps[p]==d,p\n        else:\n            assert sha(p)==d,p;deps[p]=d")
s=change(s,"The new150 clauses and conditional transfer are freshly checked; the core contradiction remains separate.",
    "The complete151 core contradiction and150 conditional actual-snake implication are imported with exact receipts. The new152 closed actual-snake consequence is checked only after the complete replay audit.")
dest=H/'scripts/check_complete.py';assert not dest.exists();dest.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_GUARDED_FINAL_ACTUAL_SNAKE_CHECKER',
    source_files_sha256={str(p):sha(p) for p in [old,T/'data/semantic-plan.json',source,out,dest,Path(__file__)]},
    complete_replay_required=True,complete_audit_required=True,checked=False)
(H/'data/completion-preparation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['status'])
