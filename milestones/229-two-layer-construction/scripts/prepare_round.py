"""Prepare width 46 with the correct preceding cover and actual crossing ports."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/228-wider-replacement-constructions'
for name in ['data','logs','lean','build']: (H/name).mkdir(exist_ok=True)
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=Path('D:/Codex/2026-10-13/new-chat/outputs')/name
    assert p.read_bytes()==(R/'paper'/name).read_bytes()
    (H/'data'/(name+'.before.txt')).write_bytes(p.read_bytes())
for name in ['native_resources.py','check_core.py','prepare_proof.py','prepare_width.py','archive_models.py','publication.py']:
    (H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
(H/'data/coverage45.json').write_bytes((P/'data/coverage45.json').read_bytes())
s=(P/'scripts/prepare_lower_pairs.py').read_text(encoding='utf-8')
s=s.replace('regions45.json','regions46.json').replace('baseline45.json','baseline46.json')
s=s.replace("result['status']=='PARTIAL_TERMINAL_RESULTS_RECORDED'","result['status']=='STATIC_BASELINE'")
old='allowed=low-(projections-{s,t})'
assert s.count(old)==1
s=s.replace(old,"own_ports=({s} if a else set()) | ({t} if b else set())\n            allowed=low-(projections-own_ports)")
(H/'scripts/prepare_lower_pairs.py').write_text(s,encoding='utf-8')
s=(P/'scripts/prepare_boundary_pairs.py').read_text(encoding='utf-8')
s=s.replace('regions45.json','regions46.json').replace('coverage44.json','coverage45.json')
s=s.replace("raw['width']==45","raw['width']==46").replace("closure['width']==44","closure['width']==45")
s=s.replace("width=45","width=46").replace('Width45 only','Width46 only').replace('native44closure','native45closure')
(H/'scripts/prepare_boundary_pairs.py').write_text(s,encoding='utf-8')
for name in ['joint_boundary.py','run_boundary.py']:
    s=(P/'scripts'/name).read_text(encoding='utf-8').replace('coverage44.json','coverage45.json').replace('native44exclusion','native45exclusion').replace('width45contexts','width46contexts')
    if name=='joint_boundary.py':
        old="assert closure['status']=='COMPLETE_NATIVE_EXCLUSION'"
        s=s.replace(old,old+" and closure['width']==45 and a.width==46")
    (H/'scripts'/name).write_text(s,encoding='utf-8')
s=(P/'scripts/prepare_pair_model.py').read_text(encoding='utf-8').replace('regions45.json','regions46.json')
(H/'scripts/prepare_pair_model.py').write_text(s,encoding='utf-8')
s=(H/'scripts/publication.py').read_text(encoding='utf-8').replace('Round228 research','Round229 research')
(H/'scripts/publication.py').write_text(s,encoding='utf-8')
pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [P/'data/completion.json',P/'data/coverage45.json',Path(__file__)]}
assert json.loads((P/'data/completion.json').read_bytes())['status']=='PROGRESS'
(H/'data/preparation.json').write_text(json.dumps(dict(previous_round_status='PROGRESS',width=46,previous_cover=45,pins=pins),indent=2)+'\n',encoding='utf-8')
print('PREPARED_ROUND229')
