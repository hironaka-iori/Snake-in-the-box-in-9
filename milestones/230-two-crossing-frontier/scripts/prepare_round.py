"""Prepare only the eleven open contexts for exactly two total crossings."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/229-two-layer-construction'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
for name in ['native_resources.py','check_core.py','prepare_proof.py','archive_models.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
for name in ['regions46.json','free-summary.json','two-crossing-frontier.json']:(H/'data'/name).write_bytes((P/'data'/name).read_bytes())
raw=read(H/'data/regions46.json');front=read(H/'data/free-summary.json');targets=read(H/'data/two-crossing-frontier.json')
assert read(P/'data/completion.json')['status']=='PROGRESS'
assert all(sha(p)==h for p,h in front['pins'].items()) and all(sha(p)==h for p,h in targets['pins'].items())
assert [r['context'] for r in targets['contexts']]==front['unresolved'] and len(front['unresolved'])==11
rows=[]
for row in raw['contexts']:
    row=dict(row);row['status']='OPEN' if row['id'] in front['unresolved'] else 'PRIOR_UNRESTRICTED_EXCLUDED';rows.append(row)
base=dict(status='STATIC_BASELINE',width=46,total_crossings=2,contexts=rows,pins={str(p):sha(p) for p in [H/'data/regions46.json',H/'data/free-summary.json',H/'data/two-crossing-frontier.json',Path(__file__)]},scope='Only11 still-open contexts are prepared for exacttwo. Other304 are already excluded for every crossing count. Original replacement_crossings field retains its4-fixed convention; lower preparation subtracts2. No boundary-change cut.')
(H/'data/baseline46.json').write_text(json.dumps(base,indent=2)+'\n',encoding='utf-8')
s=(P/'scripts/prepare_lower_pairs.py').read_text(encoding='utf-8')
old="budget=row['replacement_crossings'];choices=[];desired=[]";assert s.count(old)==1
s=s.replace(old,"budget=row['replacement_crossings']-2;assert budget>=0\n    choices=[];desired=[]")
s=s.replace("status='COMPLETE_FOR_REDUCIBLE_CONTEXTS',width=w,","status='COMPLETE_FOR_REDUCIBLE_CONTEXTS',width=w,total_crossings=2,")
(H/'scripts/prepare_lower_pairs.py').write_text(s,encoding='utf-8')
(H/'scripts/run_preparation.py').write_bytes((P/'scripts/run_preparation.py').read_bytes())
s=(H/'scripts/publication.py').read_text(encoding='utf-8').replace('Round229 research','Round230 research');(H/'scripts/publication.py').write_text(s,encoding='utf-8')
print('PREPARED_ROUND230_EXACT_TWO')
