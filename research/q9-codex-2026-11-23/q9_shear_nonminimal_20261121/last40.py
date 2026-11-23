from direct import *
from detour_cad import solve as cad
recs=list(map(json.loads,(D/'wide.jsonl').read_text().splitlines()))
for row in map(json.loads,(D/'retrywide.log').read_text().splitlines()):
 k,i,st,w=row
 if st!='UNKNOWN':continue
 i,c,ds,l=recs[k];det={int(x):v for x,v in ds.items()};st,p=cad(c['p'],c['L'],c['R'],l,c['rem']-l,det,80000)
 print(json.dumps([k,i,st,p],separators=(',',':')),flush=True)
 if p:assert len(p)==193;break
