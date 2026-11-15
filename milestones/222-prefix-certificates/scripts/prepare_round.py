from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/221-square-parity'
for x in ['scripts','data','logs','lean','build']:(H/x).mkdir(exist_ok=True)
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','import_proof.py','publication.py']:
 s=(P/'scripts'/name).read_text(encoding='utf-8').replace('Round221','Round222')
 (H/'scripts'/name).write_text(s,encoding='utf-8',newline='\n')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 (H/'data'/('before-'+name)).write_bytes((Path('D:/Codex/2026-10-13/new-chat/outputs')/name).read_bytes())
head=subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0','rev-parse','HEAD'],cwd=R,text=True).strip()
intent=dict(round=222,started_utc=datetime.now(timezone.utc).isoformat(),previous_goal_turn='PROGRESS',goal_state='ACTIVE',main_at_start=head,contributor_at_start='b0521e1d14fd52c62db4cdeccc356b70a623eb82',hypothesis='Fixing short actual prefixes may remove much of the fractional freedom that persists after all three complete inequality families. A bounded-depth reduction need not exclude every93-edge partner.',pause_policy='Continue until an exceptional result or prolonged stagnation in user/own work warrants the authorized pause; contributor work alone is not a trigger.',email_sent=False,next_full_paper_review=230)
(H/'data/round-intent.json').write_text(json.dumps(intent,indent=2)+'\n',encoding='utf-8')
print('ROUND222_PREPARED',head)
