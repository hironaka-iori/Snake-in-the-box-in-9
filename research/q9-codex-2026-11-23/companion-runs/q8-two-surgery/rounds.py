import time,sys,json,subprocess,concurrent.futures
from pathlib import Path
r=Path(__file__).resolve().parent
jobs=[('strict1',1,1.12,140000,765911),('free1',0,.97,60000,971113),('strict2',1,.78,22000,115709),('free2',0,1.55,260000,784521)]
def run(job):
 nm,mode,t,reset,seed=job
 with (r/(nm+'.pts')).open('w') as f,(r/(nm+'.log')).open('w') as g:subprocess.run([r/'search',r/'seed.pts','185',str(seed),str(t),str(reset),str(mode)],stdout=f,stderr=g,check=True)
 return nm,(r/(nm+'.log')).read_text()
with concurrent.futures.ThreadPoolExecutor(2) as pool:
 for z in pool.map(run,jobs):print(z,flush=True)
