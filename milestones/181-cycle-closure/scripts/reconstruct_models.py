"""Check saved assignments and independently count all physical square shares."""
from pathlib import Path
import gzip,json,itertools,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1];old=R/'milestones/180-share14-certificates'
meanings=json.loads(gzip.decompress((old/'certificates/012301.meanings.json.gz').read_bytes()))['meaning']
window=json.loads((old/'data/012301.json').read_text())['window'];C=window[1:-1]
records=[]
for label,stdout,cnf in [('original',old/'logs/012301.stdout',old/'certificates/012301.cnf.gz'),('closed',H/'logs/stream14.stdout',H/'certificates/012301-closed.cnf.gz')]:
 assignment={}
 for line in stdout.read_text().splitlines():
  if line.startswith('v '):
   for x in map(int,line[2:].split()):
    if x:assignment[abs(x)]=x>0
 with gzip.open(cnf,'rt') as f:
  header=f.readline().split();nv,nc=map(int,header[2:]);num=0
  for line in f:
   vals=list(map(int,line.split()));assert vals[-1]==0
   assert any(assignment[abs(x)]==(x>0) for x in vals[:-1]);num+=1
 assert num==nc and len(assignment)==nv
 S={int(v[1]) for k,v in meanings.items() if v[0]=='p' and assignment[int(k)]}
 if label=='closed':assert 4 not in S and 8 not in S
 deg=[sum((q^(1<<a)) in S for a in range(9)) for q in range(512)];empty=[0]*512
 for v in range(512):
  for a,b in itertools.combinations(range(9),2):
   if (v>>a)&1 or (v>>b)&1:continue
   sq=[v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)]
   if all(q not in S for q in sq):
    for q in sq:empty[q]+=1
 shares=[sum(12*empty[c^(1<<a)]//deg[c^(1<<a)] for a in range(9)) for c in C]
 assert sum(shares)<=13
 seen=set();components=[]
 for v in sorted(S):
  if v in seen:continue
  todo=[v];comp=[]
  while todo:
   x=todo.pop()
   if x in seen:continue
   seen.add(x);comp.append(x);todo.extend(x^(1<<a) for a in range(9) if x^(1<<a) in S)
  components.append({'vertices':sorted(comp),'degrees':[deg[x] for x in sorted(comp)],'cycle':all(deg[x]==2 for x in comp)})
 qset={c^(1<<a) for c in C for a in range(9)}
 loss=sum(12*empty[q]%deg[q] if deg[q] else 12*empty[q] for q in range(512))
 local=sum(12*empty[q]%deg[q] for q in qset)
 from fractions import Fraction
 rational=sum((Fraction(12*empty[q],deg[q]) for c in C for q in [c^(1<<a) for a in range(9)]),Fraction(0))
 wcomp=next(c for c in components if window[0] in c['vertices']);assert all(v in wcomp['vertices'] for v in window)
 record={'label':label,'status':'PASS_ALL_CLAUSES_AND_PHYSICAL_SQUARE_COUNT','selected':sorted(S),'selected_count':len(S),'centres':C,'shares':shares,'share_total':sum(shares),'rational_share':str(rational),'window_neighbour_loss':local,'global_loss':loss,'cycle_lengths':[len(c['vertices']) for c in components if c['cycle']],'window_component':wcomp,'components':components,'cnf_archive_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest()}
 records.append(record)
 print(label,'share',record['share_total'],'rational',str(rational),'local loss',local,'window component',len(wcomp['vertices']),'cycle',wcomp['cycle'],flush=True)
(H/'data/models.json').write_text(json.dumps(records,indent=2)+'\n')
