from pathlib import Path
import json,sys,os
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from search_q9_shell_dual import solve
rows=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
num=sys.argv[1] if len(sys.argv)>1 else '7'
os.environ['Q9_SHELL_PARTS']=num
os.environ['Q9_SHELL_CERT_DIR']=str(D) if num=='7' else str(D/('dual'+num))
for row in (list(map(int,sys.argv[3].split(','))) if len(sys.argv)>3 else range(4)):
 for ep in (list(map(int,sys.argv[2].split(','))) if len(sys.argv)>2 else (0,1) if num=='7' else (0,)):
  L=set(rows[row]['lower']);T={v for v in L if sum((v^(1<<k)) in L for k in range(8))<2}
  domain=L|{256+v for v in range(256) if v not in L or v in T}
  print(json.dumps(solve((row,sorted(L),0,ep,192,300000 if num!='7' else 35000,L,domain))),flush=True)
