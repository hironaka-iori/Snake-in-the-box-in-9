from pathlib import Path
from collections import Counter
from itertools import combinations
from random import Random
from time import monotonic
import csv,gzip,json,sys,hashlib
r=Path(__file__).resolve().parent;ws=Path('/Users/yichenzhan/Documents/ChatGPT/snake-in-the-box');sys.path.insert(0,str(ws))
from search_q9_anchored_sets import search
def key(p):
 def norm(a):
  m={};return bytes(m.setdefault(x^y,len(m)) for x,y in zip(a,a[1:]))
 return min(norm(p),norm(p[::-1]))
def valid(p):
 return len(set(p))==len(p) and all(0<=v<512 for v in p) and all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def prepare():
 refs={}
 for l in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt'):
  p=list(map(int,l.split()))
  if len(p)==192:refs.setdefault(key(p),p)
 assert len(refs)==131
 for p in refs.values():assert valid(p)
 knownfrags={L:{key(p[i:i+L]) for p in refs.values() for i in range(len(p)-L+1)} for L in (9,15,25,39)}
 pool={}
 for f in ('q9_all190_20261119.csv','q9_beam190_20261119.csv','q9_nonlocal189_seeds19.csv'):
  for row in csv.DictReader(open('/tmp/'+f)):
   p=list(map(int,row['vertices'].split()));pool.setdefault(key(p),p)
 data=[]
 for p in pool.values():
  assert len(p)<=191 and valid(p)
  spans=[]
  for L in knownfrags:
   spans=[(i,L) for i in range(len(p)-L+1) if key(p[i:i+L]) not in knownfrags[L]]
   if spans:break
  if spans:data.append([p,spans])
 (r/'seeds.json').write_text(json.dumps(data,separators=(',',':')))
 (r/'reference.json').write_text(json.dumps(list(refs.values()),separators=(',',':')))
 print('source_classes',len(pool),'parents_with_absent_factor',len(data),'edges',dict(Counter(len(a)-1 for a,b in data)),'minimum_private_factor_vertices',dict(Counter(s[0][1] for p,s in data)))
def code(rng):
 cols=rng.sample(range(1,16),9);syn=[0]*512
 for i in range(1,512):syn[i]=syn[i&(i-1)]^cols[(i&-i).bit_length()-1]
 assert len(set(syn))==16
 return cols,syn
def model(rng,p,spans,nfree,syn,mode):
 t,L=rng.choice(spans);anchor=set(p[t:t+L]);used=set(p);ends=(p[0],p[-1]);force=set();release=set()
 if mode:
  candidates=[]
  for e in ends:
   for d in range(9):
    v=e^(1<<d)
    if v in used:continue
    conflicts={x for x in used if x!=e and (x^v).bit_count()==1}
    if conflicts & anchor:continue
    candidates.append((e,v,conflicts))
  if not candidates:return
  rng.shuffle(candidates);candidates.sort(key=lambda x:len(x[2])+rng.random()*2.3)
  chosen=[candidates[0]]
  if mode==2:
   side=[a for a in candidates if a[0]!=chosen[0][0] and (a[1]^chosen[0][1]).bit_count()>1]
   if side:chosen.append(side[0])
  for e,v,clashes in chosen:
   force.update((v,e));release.update(syn[x] for x in clashes);release.add(syn[v])
  if force&set.union(set(),*(a[2] for a in chosen)):return
 extra=list(set(range(16))-release);rng.shuffle(extra);release.update(extra[:max(0,nfree-len(release))])
 if len(release)>11:return
 free={x for x in range(512) if syn[x] in release};F=(used-free)|anchor|force
 return F,free|F,sorted(release),[t,L],sorted(force)
def extend(p):
 out=[]
 for q in (p,p[::-1]):
  for d in range(9):
   v=q[-1]^(1<<d)
   if v not in q and all((x^v).bit_count()>1 for x in q[:-1]):out.append(q+[v])
 return out
def control():
 refs=json.loads((r/'reference.json').read_text());out=[]
 for i,p in enumerate(refs[:5]):
  rng=Random(1001+i);cols,syn=code(rng);pre=p[:-1];R={syn[p[-1]],syn[p[-4]],syn[p[-12]],syn[p[45]],syn[p[93]]}
  F={x for x in pre if syn[x] not in R};allow=F|{x for x in range(512) if syn[x] in R};st,w=search(F,set(pre),191,50000,allowed=allow,at_least=True)
  assert w and valid(w) and len(w)>=192 and F<=set(w)<=allow;out.append([cols,sorted(R),w])
 (r/'control.json').write_text(json.dumps(out));print('verified_191',len(out))
def run(tag,limit,cap,secs,off):
 refs={key(p) for p in json.loads((r/'reference.json').read_text())};data=json.loads((r/'seeds.json').read_text());rng=Random(381941+off)
 counts=Counter();start=monotonic();goals=Counter()
 with (r/(tag+'.jsonl')).open('w',1) as log:
  for z in range(limit):
   idx=rng.randrange(len(data));p,spans=data[idx];cols,syn=code(rng);num=rng.choice([4,5,6,7,8] if off%2==0 else [6,7,8,9]);mode=(z+off)%3
   inst=model(rng,p,spans,num,syn,mode)
   if not inst:continue
   F,allowed,R,span,forces=inst;goal=191 if z%5 else 192
   st,w=search(F,set(p),goal,cap,allowed=allowed,at_least=True);counts[st]+=1;goals[goal]+=1
   if w:
    assert valid(w) and len(w)>=goal+1 and F<=set(w)<=allowed and (len(w)>192 or key(w) not in refs)
    x=extend(w);assert all(valid(q) for q in x);(r/(tag+'-positive.json')).write_text(json.dumps({'parent':idx,'vertices':w,'one_step_extensions':x,'span':span}))
   print(json.dumps([idx,cols,R,span,forces,goal,st,w],separators=(',',':')),file=log)
   if w or monotonic()-start>=secs:break
 print(dict(counts),'goals',dict(goals))
if __name__=='__main__':
 if sys.argv[1]=='prep':prepare()
 elif sys.argv[1]=='ctrl':control()
 else:run(sys.argv[1],*map(int,sys.argv[2:]))

