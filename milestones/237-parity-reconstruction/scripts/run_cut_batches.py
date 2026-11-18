"""Replay small literal cut modules serially under the retained resource guards."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, time
H = Path(__file__).resolve().parents[1]
R = H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=700);args=ap.parse_args()
plan=json.loads((H/'data/cut-batches.json').read_bytes())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert all(sha(p)==h for p,h in plan['original_pins'].items())
started=time.monotonic(); done=[]; report=H/'data/cut-replay-progress.json'
status='RUNNING'
for g in plan['groups']:
    if time.monotonic()-started >= args.seconds:
        status='TIME_LIMIT';break
    name=g['module'];assert sha(H/'lean'/(name+'.lean'))==g['source_sha256']
    receipt=H/'data'/(name+'-audit.json')
    if not receipt.exists():
        result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/prepare_proof.py'),name],cwd=R,capture_output=True,text=True)
        if result.returncode:
            print(result.stdout,result.stderr,flush=True);status='PREPARATION_FAILED';break
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),name,'--timeout','60'],cwd=R,capture_output=True,text=True)
    if result.returncode:
        print(result.stdout,result.stderr,flush=True);status='CHECK_FAILED';break
    a=json.loads(receipt.read_bytes())
    assert a['status']=='PASS' and len(a['axioms'])==len(g['indices'])
    assert {x['theorem'] for x in a['axioms']}=={f'cut237_{i:03}' for i in g['indices']}
    done.append(dict(module=name,indices=g['indices'],receipt_sha256=sha(receipt)))
    report.write_text(json.dumps(dict(status='RUNNING',modules=done,seconds=time.monotonic()-started),indent=2)+'\n',encoding='utf-8')
    print('ACCEPTED',name,'total',sum(len(x['indices']) for x in done),flush=True)
else: status='PASS'
out=dict(status=status,modules=done,statements=sum(len(x['indices']) for x in done),seconds=time.monotonic()-started,plan_sha256=sha(H/'data/cut-batches.json'),runner_sha256=sha(__file__),scope='Closed numerical inequalities checked in Lean with standard axiom reports. Graph reindexing and saved-bank coverage remain separate obligations.')
report.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
if status=='PASS':
    assert out['statements']==623 and {i for g in done for i in g['indices']}==set(range(623))
    (H/'majority/kernel-cuts.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(status,'statements',out['statements'],flush=True)
