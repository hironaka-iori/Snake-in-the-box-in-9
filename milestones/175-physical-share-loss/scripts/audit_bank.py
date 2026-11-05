from pathlib import Path
from itertools import combinations
import json,hashlib,time
h=Path(__file__).resolve().parents[1];r=h.parents[1];start=time.monotonic()
p=r/'work/bank9.json';raw=p.read_bytes();bank=json.loads(raw);rows=[]
for k,row in enumerate(bank):
 v=row['vertex_sequence'];S=set(v);assert len(S)==len(v)==192
 for i,x in enumerate(v):
  assert {x^(1<<a) for a in range(9)}&S==set(v[max(0,i-1):i]+v[i+1:i+2])
 alpha=[sum(all(y not in S for y in [x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b)]) for a,b in combinations(range(9),2)) for x in v]
 assert alpha[0]>=4 and alpha[-1]>=4
 assert all(a!=1 or b>=4 for a,b in zip(alpha,alpha[1:]))
 assert all(b!=1 or a>=4 for a,b in zip(alpha,alpha[1:]))
 assert all(alpha[i:i+3]!=[2,2,2] for i in range(1,len(v)-3))
 six=min(sum(alpha[i:i+6]) for i in range(1,len(v)-6))
 seven=min(sum(alpha[i:i+7]) for i in range(1,len(v)-7))
 bounds6=[sum(alpha[:7])+alpha[-1],sum(alpha[-7:])+alpha[0]]
 bounds7=[sum(alpha[:8])+alpha[-1],sum(alpha[-8:])+alpha[0]]
 assert six>=14 and seven>=16 and min(bounds6)>=22 and min(bounds7)>=24
 rows.append({'index':k,'six_minimum':six,'seven_minimum':seven,'six_boundary':bounds6,'seven_boundary':bounds7})
 assert time.monotonic()-start<60
out={'status':'PASS_BANK_BOUNDARY_AUDIT','scope':'131 known 191-edge paths only; no universal sharpness or length bound established by this scan.','source_sha256':hashlib.sha256(raw).hexdigest(),'seconds':time.monotonic()-start,'count':len(rows),'minimum_six':min(x['six_minimum'] for x in rows),'minimum_seven':min(x['seven_minimum'] for x in rows),'minimum_six_boundary':min(min(x['six_boundary']) for x in rows),'minimum_seven_boundary':min(min(x['seven_boundary']) for x in rows),'rows':rows}
(h/'data/bank-boundary-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print({k:v for k,v in out.items() if k!='rows'})
