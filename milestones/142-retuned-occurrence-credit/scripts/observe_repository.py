"""Fetch and save the repository tips before the checkpoint commit."""
from pathlib import Path
import datetime,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
p=H/'data/repository-check.json';assert not p.exists()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
r=subprocess.run(g+['fetch','origin'],cwd=R,capture_output=True,text=True,check=True)
out=lambda args:subprocess.check_output(g+args,cwd=R,text=True).strip()
j=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),fetch_exit_code=r.returncode,
 fetch_stdout=r.stdout,fetch_stderr=r.stderr,head=out(['rev-parse','HEAD']),
 branch=out(['branch','--show-current']),origin_main=out(['rev-parse','origin/main']),
 remote_tips=out(['for-each-ref','--format=%(refname) %(objectname)','refs/remotes/origin']))
assert j['head']==j['origin_main']=='a42168ba3c810068bc9961849a6a9c6f7c618710'
p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:j[k] for k in ['head','origin_main','fetch_exit_code']}))
