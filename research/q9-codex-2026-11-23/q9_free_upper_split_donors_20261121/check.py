from pathlib import Path
import json,sys,collections
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R))
from verify_q9_high_port_whole import value
def check(p,L,cross):
 assert all(0<=x<512 for x in p) and len(p)==len(set(p)) and {x for x in p if x<256}==L
 for j,v in enumerate(p):
  ns={v^(1<<k) for k in range(9)}
  assert ns&setp==set(p[max(0,j-1):j]+p[j+1:j+2])
 assert sum((x^y)==256 for x,y in zip(p,p[1:]))==cross
def load(name):return [json.loads(s) for s in (D/name).read_text().splitlines()]
def pth(w):
 p=[0]
 for k in w:p.append(p[-1]^(1<<int(k)))
 return p
data=load('cases.jsonl');words=(R/'q8_catalogue_96_98.words').read_text().split();L={};cx={};report={}
for r in data:
 p=pth(words[r['row']]);v={x for j,x in enumerate(p) if j not in r['holes']};assert v==set(r['lower']) and len(p)-1==r['edges']
 L[r['id']]=v;cx[r['id']]=2*len(r['holes'])
assert len({tuple(sorted(v)) for v in L.values()})==len(data)
report['cases']={'rows':len({r['row'] for r in data}),'systems':len(data),'holes':dict(collections.Counter(len(r['holes']) for r in data))}
controls=json.loads((D/'controls.json').read_text())
for r in controls:L[-r['ref']]=set(r['lower']);cx[-r['ref']]=2
for mode in ['beam','focused']:
 best=-1;cnt=0;calls=0;states=0;ids=set();bests={}
 for s in (D/(mode+'.log')).read_text().splitlines():
  i,n,m,k,*p=map(int,s.split());assert i not in ids;ids.add(i)
  if i>=0:calls+=n;states+=m
  assert len(p)-1==k
  if not p:continue
  setp=set(p);check(p,L[i],cx[i])
  if i>=0:
   cnt+=1;best=max(best,k)
   if cx[i] not in bests or k>bests[cx[i]][0]:bests[cx[i]]=[k,i]
 report[mode]=dict(cases=sum(i>=0 for i in ids),valid=cnt,bridges=calls,expanded=states,best=best,best_cross=bests)
control=[]
for s in (D/'control.log').read_text().splitlines():
 ref,warm,t,st,conf,*p=s.split();p=list(map(int,p));setp=set(p);check(p,L[-int(ref)],2);assert len(p)>int(t) and st=='FOUND'
 control.append([int(ref),warm,len(p)-1])
report['controls']=control
st=(D/'native.log').read_text().splitlines();assert st[-1]=='DONE' and len(st)==len(data)+1 and set(range(len(data)))=={int(s.split()[0]) for s in st[:-1]}
report['SAT']=dict(collections.Counter(s.split()[2] for s in st[:-1]))
fac=[]
for fd,folder in [('factors.log','.'),('factors16.log','dual16'),('factors16odd.log','dual16'),('factorsbest.log','dual16')]:
 for i,_,ep,g,st,num,wit in load(fd):
  assert wit is None and g==192
  low=L[i];T={v for v in low if sum((v^(1<<k)) in low for k in range(8))<2};dom=low|{256+v for v in range(256) if v not in low or v in T}
  c=json.loads((D/folder/f'r0_goal192_parent{i}_e{ep}.json').read_text());assert set(c['parent'])==low and c['end_colour']==ep and value(c,low,dom,192,ep)==num==c['upper']
  if st=='DUAL_EXCLUSION':assert num<193*c['scale']
  fac.append([i,ep,len(c['axes']),st,num])
report['factors']=fac
print(json.dumps(report,indent=2))
