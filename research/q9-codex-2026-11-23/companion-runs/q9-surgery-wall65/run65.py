import concurrent.futures,subprocess,time,json,datetime
from pathlib import Path
r=Path(__file__).resolve().parent
jobs=[('A',37700000,2917326011,.17,1.21),('B',83000000,1774397013,0,1.76)]
def run(job):
 n,period,seed,bias,temp=job;start=time.time()
 cmd=[str(r/'run'),str(r/(n+'.txt')),str(r/'known191.txt'),'9000000000000',str(period),str(seed),str(bias),str(temp),'1',str(r/(n+'.ckpt')),'3900','90']
 with (r/(n+'.log')).open('a') as f: result=subprocess.run(cmd,stdout=f,check=True)
 return dict(id=n,start_unix=start,end_unix=time.time(),args=cmd)
start=time.time();(r/'launch.json').write_text(json.dumps(dict(start_unix=start,start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),deadline_unix=start+3900,wall_seconds=3900,max_workers=2,jobs=jobs),indent=1)+'\n')
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:results=list(p.map(run,jobs))
(r/'completed.json').write_text(json.dumps(results,indent=1)+'\n')
print(results,flush=True)
