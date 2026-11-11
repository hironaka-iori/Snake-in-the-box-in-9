from pathlib import Path
import json,subprocess,sys,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';start=time.monotonic();runs=[]
for name in json.loads((H/'data/square-order.json').read_text()):
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),name],cwd=R,check=False)
    runs.append({'module':name,'exit_code':result.returncode})
    if result.returncode:break
(H/'data/square-batch.json').write_text(json.dumps({'runs':runs,'complete':len(runs)==20 and all(r['exit_code']==0 for r in runs),'seconds':time.monotonic()-start},indent=2)+'\n');(H/'scripts/run_square.py').write_bytes(Path(__file__).read_bytes())
raise SystemExit(runs[-1]['exit_code'])
