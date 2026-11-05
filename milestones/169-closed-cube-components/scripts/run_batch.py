import time,subprocess,sys,json
from pathlib import Path
from native_resources import snapshot
h=Path(__file__).resolve().parents[1]
modules=['EightCycle168','Snake9','PathStructure','CubeLocal','Undominated167','CubeUndominated168','PathClosure169']
record={'status':'RUNNING','attempts':[]};out=h/'data/batch-run.json';deadline=time.monotonic()+90
for module in modules:
    while True:
        s=snapshot()
        if s['errors'] or s['processes']:
            record['status']='RESOURCE_CONFLICT';break
        if s['free_bytes']>=1024**3+32*1024**2:break
        if time.monotonic()>=deadline:
            record['status']='STARTUP_MEMORY_UNAVAILABLE';break
        out.write_text(json.dumps(record,indent=2)+'\n');time.sleep(2)
    if record['status']!='RUNNING':break
    c=subprocess.run([sys.executable,'-B','-X','utf8',str(h/'scripts/check_local.py'),module],capture_output=True,text=True)
    record['attempts'].append(dict(module=module,returncode=c.returncode,output=c.stdout+c.stderr))
    print(module,c.returncode,c.stdout.strip(),flush=True)
    if c.returncode:record['status']='STOPPED_ON_FAILURE';break
else:record['status']='PASS'
out.write_text(json.dumps(record,indent=2)+'\n');print(record['status'],flush=True)
