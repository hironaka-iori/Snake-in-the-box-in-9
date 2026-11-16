from pathlib import Path
import json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H.parent/'232-minority-contraction'
for d in ['scripts','data','logs','lean','build']:(H/d).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','archive_models.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
s=(H/'scripts/publication.py').read_text(encoding='utf-8').replace('Round232 research','Round233 research');(H/'scripts/publication.py').write_text(s,encoding='utf-8')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name;assert p.read_bytes()==(R/'paper'/name).read_bytes();(H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
s=(P/'scripts/run_minority.py').read_text(encoding='utf-8').replace('minority.py','lift_search.py').replace("H/'data/bases.json'","R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'")
(H/'scripts/run_lift.py').write_text(s,encoding='utf-8')
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
out=dict(round=233,started_utc='2026-11-16 14:03:02 UTC',previous_round='PROGRESS',goal_status='ACTIVE',pause_after_round=233,head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),hypothesis='Parity lift of a lower-dimensional snake, retaining all but r parent vertices as one selected colour class, admits a Hamiltonian contraction and therefore2m-2r edges. Test r0,1,2 on saved dimensions5,6,7,8. The numerical r1 pattern26->50->98 predicts194 only if actual constructions exist.',deferred='The larger single-exchange minority-class survey remains unsearched; this smaller dimension-building family first examines a specific mechanism for the observed near-doubling.')
(H/'data/resume.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PREPARED_ROUND233')
