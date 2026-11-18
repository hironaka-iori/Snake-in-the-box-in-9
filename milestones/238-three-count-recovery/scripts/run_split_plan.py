"""Check a saved finite-case split sequentially, retaining each accepted receipt."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--plan',required=True);ap.add_argument('--tag',required=True);a=ap.parse_args()
assert re.fullmatch(r'[a-z0-9-]+\.json',a.plan) and re.fullmatch(r'[a-z0-9-]+',a.tag)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
path=H/'logs'/a.plan;plan=json.loads(path.read_bytes());rows=[];start=time.monotonic()
assert all(sha(H/'lean'/(n+'.lean'))==v for n,v in plan['source_hashes'].items())
status='RUNNING'
for name in plan['modules_in_order']:
    receipt=H/'data'/(name+'-audit.json')
    if not receipt.exists():
        p=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/prepare_proof.py'),name],cwd=R,capture_output=True,text=True)
        if p.returncode:print(p.stdout,p.stderr,flush=True);status='PREPARATION_FAILED';break
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),name,'--timeout','60'],cwd=R,capture_output=True,text=True)
    print(p.stdout,p.stderr,flush=True)
    if p.returncode:status='CHECK_FAILED';break
    proof=json.loads(receipt.read_bytes());assert proof['status']=='PASS'
    rows.append(dict(module=name,reports=len(proof['axioms']),receipt_sha256=sha(receipt)))
else:status='PASS'
out=dict(status=status,modules=rows,seconds=time.monotonic()-start,plan_sha256=sha(path),runner_sha256=sha(__file__))
(H/'data'/(a.tag+'-replay.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(status,a.tag,'modules',len(rows),flush=True)
