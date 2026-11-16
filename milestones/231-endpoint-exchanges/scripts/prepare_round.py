from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H.parent/'230-two-crossing-frontier'
for d in ['scripts','data','logs','lean','build']:(H/d).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','archive_models.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
s=(H/'scripts/publication.py').read_text(encoding='utf-8').replace('Round230 research','Round231 research');(H/'scripts/publication.py').write_text(s,encoding='utf-8')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name
    assert p.read_bytes()==(R/'paper'/name).read_bytes()
    (H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
out=dict(round=231,started_utc='2026-11-16 13:37:19 UTC',previous_round='PROGRESS',goal_status='ACTIVE',pause_after_round=233,
    head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip(),
    hypothesis='Fix one96vertex parity class from a saved191edge snake, add one new vertex in the same class, and search Hamiltonian paths in the labelled contraction graph. Opposite parity vertices are free; no old order or crossing count is fixed.')
(H/'data/resume.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
s=(P/'scripts/run_pairs.py').read_text(encoding='utf-8').replace('pair_cp.py','survey.py')
start=s.index('pins = ');end=s.index('\nrecord = ',start)
s=s[:start]+"pins = {str(p):sha(p) for p in [Path(__file__), H/'scripts/survey.py', H/'scripts/native_resources.py', R/'milestones/203-block-symmetry/data/bank9-input.json']}"+s[end:]
s=s.replace("H/'data'/tag/'result.json'","H/'data'/(tag+'.json')")
(H/'scripts/run_survey.py').write_text(s,encoding='utf-8')
print('PREPARED_ROUND231')
