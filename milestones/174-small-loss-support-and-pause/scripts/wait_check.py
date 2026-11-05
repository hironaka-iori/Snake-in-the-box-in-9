import time,sys,subprocess,json
from pathlib import Path
from native_resources import snapshot
h=Path(__file__).resolve().parents[1];module=sys.argv[1];deadline=time.monotonic()+120;samples=[]
while True:
 s=snapshot();samples.append(s)
 if not s['errors'] and not s['processes'] and s['free_bytes']>=2*1024**3+64*1024**2:
  result=subprocess.run([sys.executable,'-B','-X','utf8',str(h/'scripts/check_mathlib.py'),module]);status='EXECUTED';break
 if time.monotonic()>=deadline:status='STARTUP_MEMORY_UNAVAILABLE';break
 time.sleep(2)
(h/'data'/f'{module}-startup.json').write_text(json.dumps({'status':status,'samples':samples},indent=2)+'\n');print(status)
