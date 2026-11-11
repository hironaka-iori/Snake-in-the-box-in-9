from pathlib import Path
import json,subprocess,sys,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';start=time.monotonic();runs=[]
for name in json.loads((H/'data/square-order.json').read_text()):
    if (H/'data'/(name+'-audit.json')).exists():continue
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),name],cwd=R,check=False)
    runs.append({'module':name,'exit_code':result.returncode})
    if result.returncode:break
out=H/'data'/('square-continuation-'+str(time.time_ns())+'.json');out.write_text(json.dumps({'runs':runs,'seconds':time.monotonic()-start},indent=2)+'\n');(H/'scripts/resume_square.py').write_bytes(Path(__file__).read_bytes())
raise SystemExit(runs[-1]['exit_code'] if runs else 0)
