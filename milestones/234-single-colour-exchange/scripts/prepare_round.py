from pathlib import Path
import json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H.parent/'233-parity-lift-construction'
for d in ['scripts','data','logs','lean','build']:(H/d).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','archive_models.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
s=(H/'scripts/publication.py').read_text().replace('Round233 research','Round234 research');(H/'scripts/publication.py').write_text(s,encoding='utf-8')
(H/'data/bases.json').write_bytes((R/'milestones/232-minority-contraction/data/bases.json').read_bytes())
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name
 assert p.read_bytes()==(R/'paper'/name).read_bytes()
 (H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
s=(P/'scripts/run_lift.py').read_text().replace('lift_search.py','exchange.py').replace("R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'","H/'data/bases.json'")
(H/'scripts/run_exchange.py').write_text(s,encoding='utf-8')
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
j=dict(round=234,previous_round_classification='PROGRESS',started_utc='2026-11-17 11:39:11 UTC',goal_status='ACTIVE',pause_request=None,head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),hypothesis='A 192-edge snake may exist after replacing one vertex of a saved 96-vertex minority class, with the opposite class and all ordering free.',scope='145 saved classes, 96 removals and 160 new same-parity insertions per class; 2227200 descriptions. No general upper-bound work.')
(H/'data/resume.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print('PREPARED_ROUND234')
