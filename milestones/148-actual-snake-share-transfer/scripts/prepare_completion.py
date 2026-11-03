"""Prepare the final composition, guarded until the complete replay succeeds."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=read(H/'data/transfer-plan-v4.json');p=H/'lean/ShareComplete148.lean'
plan.update(status='PREPARED_FINAL_COMPOSITION_REPLAY_PENDING',module_order=['ShareComplete148'],framework_modules=['ShareComplete148'],
    artifacts=[dict(module='ShareComplete148',path=p.relative_to(H).as_posix(),sha256=sha(p))],
    checked=False,selected_scope='Compile only after the exact147 full replay finishes successfully. This source is not yet an accepted unconditional share theorem.',
    preparer_sha256=sha(Path(__file__)))
out=H/'data/completion-plan.json';assert not out.exists();out.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
s=(H/'scripts/check_module_v4.py').read_text(encoding='utf-8').replace('data/transfer-plan-v4.json','data/completion-plan.json')
needle="read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))\n"
assert s.count(needle)==1
guard="""progress=read(Q/'replay/data/full-replay-progress.json')
if progress['status']!='PASS_COMPLETE_FULL_REPLAY_MODULES' or progress['active'] is not None:
    print(json.dumps(dict(status='WAITING_FOR_COMPLETE_REPLAY',replay_status=progress['status'],checked=len(progress['checked_modules']))))
    raise SystemExit(2)
assert len(progress['checked_modules'])==1789
assert not (Q/'replay/data/full-replay-batch.lock').exists()
"""
s=s.replace(needle,needle+guard)
s=s.replace("[build,Q/'build']+external","[build,Q/'build',Q/'replay/build']+external")
s=s.replace("[build,Q/'build',B.parent/'lib/lean']+external","[build,Q/'build',Q/'replay/build',B.parent/'lib/lean']+external")
s=s.replace("if not rp.exists():rp=Q/'data'/(name+'-audit.json')","if not rp.exists():rp=Q/'data'/(name+'-audit.json')\n    if not rp.exists():rp=Q/'replay/data'/(name+'-audit.json')")
s=s.replace("paths=[str(build),str(Q/'build')]","paths=[str(build),str(Q/'build'),str(Q/'replay/build')]")
dest=H/'scripts/check_complete.py';assert not dest.exists();dest.write_text(s,encoding='utf-8',newline='\n')
print('PREPARED_FINAL_COMPOSITION_REPLAY_PENDING')
