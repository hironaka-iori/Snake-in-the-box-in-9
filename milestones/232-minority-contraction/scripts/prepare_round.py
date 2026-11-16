from pathlib import Path
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H.parent/'231-endpoint-exchanges'
for d in ['scripts','data','logs','lean','build']:(H/d).mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','archive_models.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
s=(H/'scripts/publication.py').read_text(encoding='utf-8').replace('Round231 research','Round232 research');(H/'scripts/publication.py').write_text(s,encoding='utf-8')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name;assert p.read_bytes()==(R/'paper'/name).read_bytes();(H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
raw=json.loads((P/'data/colour-survey.json').read_bytes());assert raw['status']=='COMPLETE_SURVEY'
data=dict(bases=raw['bases'],pins={str(P/'data/colour-survey.json'):sha(P/'data/colour-survey.json')},scope='The145 distinct labelled96vertex classes of the131saved191edge seeds. No new graph search is performed in this extraction.')
(H/'data/bases.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
s=(P/'scripts/run_hamilton.py').read_text(encoding='utf-8').replace('hamilton.py','minority.py').replace("H/'data/colour-survey.json'","H/'data/bases.json'")
(H/'scripts/run_minority.py').write_text(s,encoding='utf-8')
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
out=dict(round=232,started_utc='2026-11-16 13:50:20 UTC',previous_round='PROGRESS',goal_status='ACTIVE',pause_after_round=233,head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),hypothesis='A fixed96vertex minority parity class may admit a Hamiltonian contraction whose endpoints have singleton-neighbour labels. Entire oppositeclass andordering are free.')
(H/'data/resume.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PREPARED_ROUND232')
