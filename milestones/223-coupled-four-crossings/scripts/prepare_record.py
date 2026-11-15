"""Preserve the round's mathematical evidence and current external revisions."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def gitout(*args):return subprocess.check_output(git+list(args),cwd=R,text=True).strip()
head=gitout('rev-parse','HEAD');contributor=gitout('rev-parse','origin/research/unconditional-241')
save(H/'data/round-intent.json',dict(round=223,previous_research_round=222,previous_research_result='PROGRESS',previous_interactive_turn='ROUTE_SELECTION_ONLY',goal_status='ACTIVE',base_head=head,contributor_revision=contributor,utc=datetime.now(timezone.utc).isoformat(),route='Joint four-crossing construction, guided by actual lower-dimensional decompositions',hypothesis='A coordinated change of both Q8 faces and free crossing ports may give 192 edges. Existence is unproved; 196 remains a stretch target.',scope='Constructive work. No upper-bound investigation. No software tests.'))
design=subprocess.check_output(git+['show',contributor+':milestones/35-231-lean/DESIGN.md'],cwd=R)
(H/'data/contributor-design.txt').write_bytes(design)
save(H/'data/github-observation.json',dict(main=gitout('rev-parse','origin/main'),contributor=contributor,design_sha256=sha(H/'data/contributor-design.txt'),observation='Contributor reports a candidate231 calculation and generic/toy Lean chain; generated tables, shards, covers, certificates and glue remain. No independent rebuild or merge performed; maintained interval unchanged.'))
results={}
for tag in ['joint-d4','joint-d8','joint-d12','endpoint80-d12']:
    data=json.loads((H/'data'/(tag+'.json')).read_bytes())
    run=json.loads((H/'data'/(tag+'-execution.json')).read_bytes())
    assert run['status']=='ACCEPTED_NATIVE_RESULT' and run['exit_code']==0 and run['stop_reason'] is None
    assert sha(H/'data'/(tag+'.json'))==run['result_sha256']
    assert all(sha(p)==d for p,d in run['pins'].items())
    results[tag]=dict(status=data['status'],seconds=data['seconds'],iterations=data['iterations'],cycle_cuts=len(data['cycle_cuts']),witness=data['witness'],result_sha256=sha(H/'data'/(tag+'.json')),execution_sha256=sha(H/'data'/(tag+'-execution.json')))
save(H/'data/search-summary.json',results)
save(H/'data/endpoint-scope.json',dict(query='endpoint80-d12',scope='Root0 and endpoint80 fixed; vertex88 retained internally. Both faces change, at most12 original vertices omitted, exactly193 selected vertices, exactlyfour bit8 crossings. All port locations variable.',metadata_note='The inherited free-endpoint phrase in the base scope string is superseded by the explicit endpoint argument and the specialized equality end[80]=1. The result scope also states this specialization. No ambiguity in the saved model constraints.',required_deletion=dict(vertex=208,reason='80 XOR 88 = 8 and 80 XOR 208 = 128. Retaining both neighbours would give endpoint80 degree at least2.')))
print(json.dumps(results),flush=True)
