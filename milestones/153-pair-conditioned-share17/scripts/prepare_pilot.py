"""Generate only the bounded initial-tree pilot for the critical certificate."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=R/'milestones/150-actual-pair-share/replay/emit_lean.py'
text=old.read_text(encoding='utf-8').replace('150','153')
needle="    args=ap.parse_args();s=json.loads((H/'data/sizing.json').read_text());r=json.loads((H/'data/packed-replay.json').read_text())"
assert text.count(needle)==1
text=text.replace(needle,"""    args=ap.parse_args()
    if args.full:
        accepted=json.loads((H/'data/pilot-completion.json').read_text())
        assert accepted['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT'
    s=json.loads((H/'data/sizing.json').read_text());r=json.loads((H/'data/packed-replay.json').read_text())""")
target=H/'replay/emit_lean.py';assert not target.exists()
target.write_text(text,encoding='utf-8',newline='\n')
subprocess.run([sys.executable,'-B','-X','utf8',str(target)],cwd=R,check=True)
out=dict(status='PREPARED_BOUNDED_PILOT_UNCOMPILED',source_files_sha256={str(p):sha(p) for p in [Path(__file__),old,target,H/'replay/data/pilot-source-plan.json']},
         full_generation_requires_accepted_pilot=True,Lean_started=False)
(H/'data/pilot-preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
