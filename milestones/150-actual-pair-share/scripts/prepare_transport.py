"""Reuse the audited streaming transport on the count-free012032 certificate."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
old=R/'milestones/147-countfree-clause-semantics/replay';dest=H/'replay'
dest.mkdir(exist_ok=False)
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def change(s,a,b):assert a in s,a;return s.replace(a,b)
meta=read(H/'data/share150.json');proof=H/'work/highpair16/trimmed.lrat'
s=(old/'prepare_replay.py').read_text(encoding='utf-8')
s=change(s,"M145 = ROOT / 'milestones/145-countfree-012301'","M145 = ROOT / 'milestones/150-actual-pair-share'")
s=change(s,"M146 = ROOT / 'milestones/146-initial-tree-and-paper'","M146 = M145")
s=change(s,"'work/conversion-long/trimmed.lrat'","'work/highpair16/trimmed.lrat'")
s=change(s,"'work/conversion-long/core-ids.json'","'work/highpair16/core-ids.json'")
s=change(s,"FULL = ROOT / 'milestones/72-four-count-proof-closure/critical-current/build/pysat3-cap15.cnf'","FULL = M145 / 'work/countfree16/original.cnf'")
s=s.replace("'data/share146.json'","'data/share150.json'").replace("'certificates/share146.cnf'","'certificates/share150.cnf'")
s=change(s,"M145/'data/direct-replay.json'","M145/'work/highpair16/native-replay.json'")
s=change(s,'7e047da8e66a46d4d283a4780d84287872b275576862b9bda01713241065d932',sha(proof))
s=change(s,'==5956','=='+str(meta['semantic_variables']))
s=change(s,'(285541,31017505,12977)','(58182,5350080,13655)')
(dest/'prepare_replay.py').write_text(s,encoding='utf-8',newline='\n')
s=(old/'transport_replay.py').read_text(encoding='utf-8').replace('unchanged145','count-free150')
s=s.replace('285541','58182').replace('31017505','5350080')
(dest/'transport_replay.py').write_text(s,encoding='utf-8',newline='\n')
pins={str(p):sha(p) for p in [Path(__file__),old/'prepare_replay.py',old/'transport_replay.py',
    dest/'prepare_replay.py',dest/'transport_replay.py',H/'data/share150.json',proof]}
(H/'data/transport-preparation.json').write_text(json.dumps(dict(status='PREPARED_TRANSPORT_NOT_RUN',source_files_sha256=pins),indent=2)+'\n',encoding='utf-8')
print('Prepared exact-input streaming transport; no solver or Lean invocation.')
