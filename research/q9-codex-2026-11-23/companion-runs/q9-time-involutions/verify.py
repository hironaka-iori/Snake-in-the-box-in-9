from pathlib import Path
from collections import Counter
from itertools import combinations
from hashlib import sha256
import json
r=Path(__file__).resolve().parent
def check(p):
 if len(set(p))!=len(p) or any(not 0<=x<=511 for x in p):return False
 return all(((p[i]^p[j]).bit_count()==1)==(j-i==1) for i,j in combinations(range(len(p)),2))
def key(p):
 def canon(q):
  m={};return tuple(m.setdefault(x^y,len(m)) for x,y in zip(q,q[1:]))
 return min(canon(p),canon(p[::-1]))
truth=[list(map(int,s.split())) for s in (r/'ctrl_truth.pts').read_text().splitlines()];inputs=[list(map(int,s.split())) for s in (r/'ctrl.pts').read_text().splitlines()]
assert len(truth)==len(inputs) and all(check(p) for p in truth) and all(not check(p) for p in inputs)
data={};total=0
for name in ['ctrl','w0','w1','w2','w3','geocontrol','geo1','geo2','geo3','geo0','full0','realctrl','fg0','fg1','fg2','fg3']:
 out=r/(name+'.out');log=r/(name+'.log')
 if not out.exists() or not log.exists() or not log.stat().st_size:continue
 rows=[];sameClass=0
 for s in out.read_text().splitlines():
  z=list(map(int,s.split()));p=z[2:];assert check(p);assert len(p)==(192 if name in ('ctrl','geocontrol','realctrl') else 193);rows.append(len(p)-1)
  if name=='ctrl':sameClass+=key(truth[z[0]])==key(p)
 data[name]={'run':log.read_text().strip(),'independent_witness_edges':dict(Counter(rows)),'out_sha256':sha256(out.read_bytes()).hexdigest()}
 if name=='ctrl':
  assert len(rows)==len(inputs)==12;data[name]['equivalent_to_original_truth']=sameClass
import gzip
known={key(q) for s in gzip.open(Path.cwd()/'q9_free_bridge_join_inputs.txt.gz','rt') if len(q:=list(map(int,s.split())))==192}
assert len(known)==131
z=list(map(int,(r/'realctrl.out').read_text().split()));out=z[2:];precursor=list(map(int,(r/'realctrl.pts').read_text().splitlines()[z[0]].split()))
assert len(precursor)==len(out)==192 and check(precursor[:-1]) and not check(precursor) and check(out)
data['natural_control']={'verified_original_190':True,'input_chords':sum((precursor[i]^precursor[j]).bit_count()==1 for i,j in combinations(range(192),2) if j>i+1),'output_is_among_131':key(out) in known}
print(data)
(r/'audit.json').write_text(json.dumps(data,indent=2)+'\n')

