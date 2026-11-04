"""Add the recorded Mathlib dependency paths for the last two unchanged modules."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def write(p,s):
    b=s.encode('utf-8')
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)
oldpath=H/'data/semantic-execution.json';old=read(oldpath)
for name in old['new_module_order'][:-2]:
    q=read(H/'data'/(name+'-audit.json'))
    assert q['status']=='PASS' and q['exit_code']==0
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
assert old['new_module_order'][-2:]==['Share144.Compose','Share144.Sat']
ep=R/'milestones/155-share17-replay/data/final-composition-plan.json';external=read(ep)
checker=(H/'scripts/check_semantic.py').read_text().replace('data/semantic-execution.json','data/semantic-final-execution.json')
driver=(H/'scripts/run_semantics.py').read_text().replace('data/semantic-execution.json','data/semantic-final-execution.json').replace('semantic-batch.lock','semantic-final-batch.lock').replace("'semantic-batch-'","'semantic-final-batch-'").replace('semantic-progress.json','semantic-final-progress.json').replace('scripts/check_semantic.py','scripts/check_semantic_final.py')
write(H/'scripts/check_semantic_final.py',checker);write(H/'scripts/run_semantics_final.py',driver)
new=dict(old);new['input_pins']=dict(old['input_pins'])
for p in [oldpath,ep,H/'scripts/check_semantic.py',H/'scripts/run_semantics.py']:new['input_pins'][str(p)]=sha(p)
for p,d in external['external_pins'].items():assert sha(p)==d,p;new['input_pins'][p]=d
new['new_module_order']=old['new_module_order'][-2:]
new['search_paths']=old['search_paths'][:2]+external['external_library_search_paths']
new['checker_sha256']=sha(H/'scripts/check_semantic_final.py');new['driver_sha256']=sha(H/'scripts/run_semantics_final.py')
new['status']='PREPARED_FINAL_ASSEMBLY_ENVIRONMENT_FIXED'
new['reason']='Original Compose imports Mathlib.Tactic, which requires recorded package paths including Batteries. Prior106 checks and source bytes are preserved.'
write(H/'data/semantic-final-execution.json',json.dumps(new,indent=2)+'\n')
print('PREPARED_TWO_FINAL_MODULES')
