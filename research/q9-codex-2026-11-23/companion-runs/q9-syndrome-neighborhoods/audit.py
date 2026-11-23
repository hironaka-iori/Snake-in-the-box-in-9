from pathlib import Path
from itertools import combinations
from collections import Counter
import json,gzip,csv
r=Path(__file__).resolve().parent
def path_ok(p):
 return len(set(p))==len(p) and all(0<=a<512 for a in p) and all(((p[i]^p[j]).bit_count()==1)==(j-i==1) for i,j in combinations(range(len(p)),2))
def canon(p):
 def orient(q):
  alphabet={};return tuple(alphabet.setdefault(q[i]^q[i+1],len(alphabet)) for i in range(len(q)-1))
 return min(orient(p),orient(p[::-1]))
def read(name):return [json.loads(l) for l in (r/name).open()]
refs=json.loads((r/'reference.json').read_text());assert all(path_ok(p) and len(p)==192 for p in refs);known=set(map(canon,refs));assert len(known)==131
seeds=json.loads((r/'seeds.json').read_text());lens={L for _,spans in seeds for i,L in spans}
lib={L:{canon(p[i:i+L]) for p in refs for i in range(len(p)-L+1)} for L in lens}
for p,spans in seeds:
 assert len(p)<=191 and path_ok(p)
 for i,L in spans:assert canon(p[i:i+L]) not in lib[L]
base={};old189=set();old190=set()
for f in ('q9_all190_20261119.csv','q9_beam190_20261119.csv','q9_nonlocal189_seeds19.csv'):
 for row in csv.DictReader(open('/tmp/'+f)):
  p=list(map(int,row['vertices'].split()));base[canon(p)]=len(p)-1
  if len(p)==191:old190.add(canon(p));old189.update((canon(p[:-1]),canon(p[1:])))
new={};absent=0
for i,goal,j,b,p,(start,L) in read('chain-seeds.jsonl'):
 assert path_ok(p) and canon(p) not in base and canon(p) not in new and canon(p[start:start+L]) not in lib[L];new[canon(p)]=goal;absent+=canon(p) not in old189
for cols,classes,w in json.loads((r/'control.json').read_text()):assert path_ok(w) and len(w)>=192
control=[list(map(int,l.split()))[3:] for l in (r/'corectrl.out').open()]
assert len(control)==4 and all(path_ok(p) and len(p)==192 for p in control)
block=json.loads((r/'blocked-control.json').read_text());assert block[0][1]=='FOUND' and path_ok(block[0][3]) and block[1][1]=='UNSAT' and block[1][2]>0
status={};outcome={}
for name in ('small','wider'):
 for i,row in enumerate(read(name+'.jsonl')):status[name,i]=row[-2]
for name,j,idx,goal,st,p in read('retry.jsonl'):assert status[name,j]=='UNKNOWN';status[name,j]=st
for name,j,idx,goal,st,p in read('deepretry.jsonl'):assert status[name,j]=='UNKNOWN';status[name,j]=st
outcome['direct_after_retry']=dict(Counter(status.values()))
for name,ii in [('cascade',-2),('blocked',4),('chain',4)]:outcome[name]=dict(Counter(rec[ii] for rec in read(name+'.jsonl')))
positive=[]
for f in r.glob('*positive.json'):
 item=json.loads(f.read_text());p=item.get('vertices') if isinstance(item,dict) else item[0];assert path_ok(p) and (len(p)>=193 or canon(p) not in known);positive.append(f.name)
for l in (r/'core.out').open():
 p=list(map(int,l.split()))[3:];assert path_ok(p) and (len(p)>192 or canon(p) not in known);positive.append('core.out')
info=dict(parent_classes=len(base),starting_edges=dict(Counter(base.values())),known_191_classes=len(known),private_parents=len(seeds),private_parent_edges=dict(Counter(len(p)-1 for p,_ in seeds)),verified_syndrome_controls=5,verified_truncated_endpoint_controls=4,withheld_191_control=[x[:3] for x in block],intermediate_classes=dict(Counter(new.values())),intermediate_189_not_trimmed_from_reference_190=absent,solver_counts=outcome,known_191_models_rejected=sum(a[5] for a in read('blocked.jsonl')),novel_191_or_higher=positive,endpoint_search_log=(r/'core.log').read_text().strip())
(r/'audit.json').write_text(json.dumps(info,indent=2)+'\n');print(info)

