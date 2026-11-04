"""Adapt the audited streaming transport to the exact critical-context proof."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
old=R/'milestones/150-actual-pair-share/replay';dest=H/'replay';dest.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def change(s,a,b):assert a in s,a;return s.replace(a,b)
meta=read(H/'data/share153.json');proof=H/'critical/work/critical17/trimmed.lrat'
s=(old/'prepare_replay.py').read_text(encoding='utf-8')
s=change(s,"'milestones/150-actual-pair-share'","'milestones/153-pair-conditioned-share17'")
s=change(s,'work/highpair16','critical/work/critical17')
s=change(s,'work/countfree16/original.cnf','critical/work/critical17/input.cnf')
s=s.replace('share150.json','share153.json').replace('share150.cnf','share153.cnf')
s=change(s,'4235b4df6ed6423a9148594572aa5f108b2106770c5dfc6b9b46cf0c9db0bf23',sha(proof))
s=change(s,'==5984','=='+str(meta['semantic_variables']))
s=change(s,'(58182,5350080,13655)','(30305,1754767,11869)')
(dest/'prepare_replay.py').write_text(s,encoding='utf-8',newline='\n')
s=(old/'transport_replay.py').read_text(encoding='utf-8')
s=s.replace('count-free150','critical-context153').replace('58182','30305').replace('5350080','1754767')
(dest/'transport_replay.py').write_text(s,encoding='utf-8',newline='\n')
pins={str(p):sha(p) for p in [Path(__file__),old/'prepare_replay.py',old/'transport_replay.py',
    dest/'prepare_replay.py',dest/'transport_replay.py',H/'data/share153.json',proof]}
(H/'data/transport-preparation.json').write_text(json.dumps(dict(status='PREPARED_TRANSPORT_NOT_RUN',source_files_sha256=pins),indent=2)+'\n',encoding='utf-8')
print('PREPARED_CRITICAL_CONTEXT_TRANSPORT')
