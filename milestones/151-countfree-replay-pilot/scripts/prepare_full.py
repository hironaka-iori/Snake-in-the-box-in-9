"""Prepare full-source generation after acceptance of the exact pilot."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/150-actual-pair-share'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def change(s,a,b):assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
done=read(H/'data/pilot-completion.json')
assert done['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT' and done['checked_modules']==38
old=P/'replay/emit_lean.py';assert sha(old)=='758e468c590be2c4c2079c26265f87161a7bccc12183deda68353a95a0d9ba25'
s=old.read_text(encoding='utf-8')
s=change(s,'import prepare_replay as p',
    "import sys\nH=Path(__file__).resolve().parents[1]\nINPUT=H.parents[1]/'milestones/150-actual-pair-share/replay'\nsys.path.insert(0,str(INPUT))\nimport prepare_replay as p")
s=change(s,"H=p.HERE; LEAN=H/'lean'; NS='Snake9.ReplayData150'","LEAN=H/'lean'; NS='Snake9.ReplayData150'")
s=change(s,"(H/'data/packed-steps.bin').open", "(INPUT/'data/packed-steps.bin').open")
s=change(s,"path=H/cp['path']","path=INPUT/cp['path']")
s=change(s,"args=ap.parse_args();s=json.loads((H/'data/sizing.json').read_text());r=json.loads((H/'data/packed-replay.json').read_text())",
    "args=ap.parse_args();assert args.full\n    accepted=json.loads((H/'data/pilot-completion.json').read_text());assert accepted['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT'\n    s=json.loads((INPUT/'data/sizing.json').read_text());r=json.loads((INPUT/'data/packed-replay.json').read_text())")
s=change(s,"for x in r['artifacts']:assert p.sha(H/x['path'])==x['sha256']","for x in r['artifacts']:assert p.sha(INPUT/x['path'])==x['sha256']")
target=H/'scripts/emit_full.py';assert not target.exists();target.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_FULL_GENERATOR_AFTER_ACCEPTED_PILOT',
    source_files_sha256={str(p):sha(p) for p in [old,P/'replay/prepare_replay.py',H/'data/pilot-completion.json',H/'data/pilot-source-plan.json',Path(__file__),target]},
    change_scope='Read exact packed input from150; write new full sources into151. Mathematical emitter templates are unchanged. Existing pilot bytes must match before any full source is written.')
(H/'data/full-generator-plan.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['status'])
