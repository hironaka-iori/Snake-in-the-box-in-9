from pathlib import Path
import json,subprocess,sys,time
H=Path(__file__).resolve().parents[1];modules=json.loads((H/'data/lower-proof-order.json').read_text());rows=[];start=time.monotonic()
for module in modules:
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),module])
    rows.append(dict(module=module,exit_code=result.returncode))
    if result.returncode:break
out=dict(status='COMPLETE' if len(rows)==len(modules) and all(r['exit_code']==0 for r in rows) else 'INCOMPLETE',rows=rows,seconds=time.monotonic()-start)
dest=H/'data'/('lower-proof-batch-'+str(time.time_ns())+'.json');dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
raise SystemExit(0 if out['status']=='COMPLETE' else 1)
