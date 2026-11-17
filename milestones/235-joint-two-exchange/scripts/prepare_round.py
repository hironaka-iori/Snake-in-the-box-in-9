from pathlib import Path
import json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H.parent/'234-single-colour-exchange'
for d in ['scripts','data','logs','lean','build']:(H/d).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','archive_models.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
s=(H/'scripts/publication.py').read_text().replace('Round234 research','Round235 research');(H/'scripts/publication.py').write_text(s,encoding='utf-8')
(H/'data/bases.json').write_bytes((P/'data/bases.json').read_bytes())
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
 (H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
s=(P/'scripts/run_exchange.py').read_text().replace('exchange.py','joint_search.py')
(H/'scripts/run_joint.py').write_text(s,encoding='utf-8')
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
j=dict(round=235,previous_round_classification='PROGRESS',started_utc='2026-11-17 12:03:09 UTC',goal_status='ACTIVE',head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),hypothesis='A 192-edge snake may exist with two replacements of a saved96vertex minority class, choosing all other vertices and order jointly.',planned_bases=[139,7,6,0],selection='Base139 has54 surviving one-exchange descriptions, tied for the largest count. Bases7 and6 also have many; base0 supplies the earliest saved comparison. This is a heuristic selection, not a symmetry cover.',reused_model='milestones/199-parent-diversity/scripts/circuit_search.py: optional selected-vertex circuit and exact induced-edge constraints. Here use all512 actual cubevertices, no quotient, crossing or endpoint restriction.')
(H/'data/resume.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print('PREPARED_ROUND235')
