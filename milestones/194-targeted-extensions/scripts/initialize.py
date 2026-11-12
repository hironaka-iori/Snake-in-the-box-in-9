from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/193-block-reroutings'
assert not (H/'data/start.json').exists()
for d in ['data','lean','build','logs']:(H/d).mkdir(exist_ok=True)
(H/'.gitattributes').write_bytes(b'* -text\n')
for name in ['check_core.py','native_resources.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
raw=(P/'data/bank9-input.json').read_bytes();(H/'data/bank9-input.json').write_bytes(raw)
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
state=dict(round=194,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),previous_turn='PROGRESS: round193 complete and published; native closure through33 and general Lean replacement criteria.',
    goal_status='active',main_head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),
    contributor_head=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip(),
    bank_sha256=hashlib.sha256(raw).hexdigest(),direction='Specified endpoint extension after a larger contiguous replacement; target192 edges.')
(H/'data/start.json').write_text(json.dumps(state,indent=2)+'\n');print(json.dumps(state))
