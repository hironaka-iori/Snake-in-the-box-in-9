"""Compile the resumed mathematical modules serially with retained guards."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('group',choices=['inverse','spectral']);a=ap.parse_args()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
if a.group=='inverse':
    plan=json.loads((H/'logs/cube-inverse-split-plan.json').read_bytes())
    names=plan['modules_in_order']
    assert all(sha(H/'lean'/(n+'.lean'))==h for n,h in plan['source_hashes'].items())
else:
    names=['ContractedDegrees237','PartialDeficit237','Cut237','CutGeometry237']
rows=[];status='RUNNING';start=time.monotonic()
for name in names:
    receipt=H/'data'/(name+'-audit.json')
    if not receipt.exists():
        p=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/prepare_proof.py'),name],cwd=R,capture_output=True,text=True)
        if p.returncode:
            status='PREPARATION_FAILED';print(p.stdout,p.stderr,flush=True);break
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),name,'--timeout','60'],cwd=R,capture_output=True,text=True)
    print(p.stdout,p.stderr,flush=True)
    if p.returncode:status='CHECK_FAILED';break
    proof=json.loads(receipt.read_bytes());assert proof['status']=='PASS'
    rows.append(dict(module=name,reports=len(proof['axioms']),receipt_sha256=sha(receipt)))
else:status='PASS'
out=dict(status=status,group=a.group,modules=rows,seconds=time.monotonic()-start,runner_sha256=sha(__file__),planned_modules=names)
(H/'data'/(a.group+'-replay.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(status,a.group,'modules',len(rows),flush=True)
