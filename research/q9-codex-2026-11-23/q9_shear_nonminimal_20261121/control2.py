from prepare import *
from detour_cad import solve
for x in map(json.loads,(D/'directcontrol.log').read_text().splitlines()):
 a=list(map(int,(OLD/'control.work').read_text().splitlines()[x['ix']].split()));p=a[9:];det={int(k):v for k,v in x['det'].items()}
 st,w=solve(p,a[5],a[6],x['l'],x['r'],det,30000)
 print(json.dumps([st,w],separators=(',',':')),flush=True)
long=(D/'long.log').read_text().splitlines()[-1].split();assert long[0]=='FOUND';g,row,d,t,a,b,pivot,e=map(int,long[1:9])
W=(R/'q9_gap_generations/prior191.words').read_text().splitlines();p=[0]
for c in W[row]:p.append(p[-1]^(1<<int(c)))
q=[v^(t if v>>d&1 else 0) for v in p[a:b+1]];st,w=solve(q,0,0,0,0,{pivot-a:e},30000)
print(json.dumps([st,w],separators=(',',':')),flush=True)
