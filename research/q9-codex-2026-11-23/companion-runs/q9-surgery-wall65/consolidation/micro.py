import json,subprocess,time,random
from pathlib import Path
r=Path(__file__).resolve().parent
jobs=[('A',6.4,2.2),('B',10.,2.4),('A',9.5,2.7),('B',6.8,2.6),('A',15.,3.1),('B',13.,3.)]
for i,(label,beta,peak) in enumerate(jobs):
    args=[r/'run',r/(label+'.txt'),r.parent/'known191.txt','150000000','8500000',str(304621319+i*607833),'0',str(peak),'1',r/('m'+str(i)+'.ckpt'),'60','20',str(beta)]
    with (r/('m'+str(i)+'.log')).open('w') as f:subprocess.run(args,stdout=f,check=True)
    lines=(r/('m'+str(i)+'.log')).read_text().splitlines();print(i,label,beta,peak,lines[-1],flush=True)
    if any(l.startswith(('TARGET','EXTENDED')) for l in lines):break
