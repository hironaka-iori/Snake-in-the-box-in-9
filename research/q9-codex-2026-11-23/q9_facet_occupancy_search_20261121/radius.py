from prepare import *
from itertools import combinations
from collections import Counter
import sys
from pysat.solvers import Minicard
def read(name):return list(map(json.loads,(D/name).read_text().splitlines()))
def elite():
 c=read('cases.jsonl');best={}
 for mode in ('cold','warm','blend'):
  for s in (D/(mode+'.log')).read_text().splitlines():
   z=s.split();i=int(z[1]);ms=z[12:20];assert len(ms)==8
   b=sum(int(v)<<(64*j) for j,v in enumerate(ms));m=format(b,'x');key=(m,c[i]['anchor'])
   best.setdefault(key,dict(id=i,mode=mode,mask=m,score=int(z[5])))
 rows=list(best.values());rows.sort(key=lambda r:(r['score'],r['id']))
 (D/'elite.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rows));return rows
def complete(c,start,k,budget,goal):
 fix=unpack(c['anchor']);dom=unpack(c['allowed']);free=dom-fix;present=set(start);ma=c['majority']
 assert len(present)==goal+1 and fix<=present<=dom
 with Minicard() as s:
  def eq(z,n):
   if not 0<=n<=len(z):s.add_clause([]);return
   s.add_atmost(z,n);s.add_atmost([-x for x in z],len(z)-n)
  for col in (0,1):
   need=(goal+1)//2+(goal%2==0 and col==ma);eq([x+1 for x in free if x.bit_count()%2==col],need-sum(x.bit_count()%2==col for x in fix))
  s.add_atmost([-x-1 for x in present-fix],k);eps=[[],[]]
  for v in dom:
   col=v.bit_count()%2;guard=[] if v in fix else [-v-1];near=N[v]&free;adj=[n+1 for n in near];degree=2-len(N[v]&fix)
   if goal%2 or col==ma:
    e=513+v;eps[col].append(e);adj.append(e)
    if v in free:s.add_clause([-e,v+1])
   if degree>len(adj):s.add_clause(guard);continue
   for group in combinations(adj,degree+1):s.add_clause(guard+[-z for z in group])
   for group in combinations(adj,len(adj)-degree+1):s.add_clause(guard+list(group))
  for col in (0,1):eq(eps[col],1 if goal%2 else 2*int(col==ma))
  s.set_phases([x+1 if x in present else -x-1 for x in free]+[(513+x)*(1 if len(N[x]&present)==1 else -1) for x in present])
  cuts=0
  while s.accum_stats()['conflicts']<budget:
   s.conf_budget(budget-s.accum_stats()['conflicts']);res=s.solve_limited()
   if res is not True:return 'UNSAT' if res is False else 'UNKNOWN',s.accum_stats()['conflicts'],cuts,None
   model=set(s.get_model());ss=fix|{v for v in free if v+1 in model};rem=set(ss);parts=[]
   while rem:
    q=[rem.pop()]
    for x in q:
     more=N[x]&rem;q.extend(more);rem-=more
    parts.append(set(q))
   if len(parts)==1:
    tips=[v for v in ss if len(N[v]&ss)==1];assert len(tips)==2
    q=tips[:1];rem=ss-{q[0]}
    while rem:
     v,=N[q[-1]]&rem;q.append(v);rem.remove(v)
    assert valid(q) and len(q)==goal+1 and len(present-ss)<=k
    return 'FOUND',s.accum_stats()['conflicts'],cuts,q
   root=min(fix)
   for part in parts:
    if root in part:continue
    border=set.union(*(N[x] for x in part))&free-part;guard=[] if part&fix else [-min(part)-1];s.add_clause(guard+[v+1 for v in border]);cuts+=1
  return 'UNKNOWN',s.accum_stats()['conflicts'],cuts,None
def main():
 c=read('cases.jsonl');mode=sys.argv[1]
 if mode=='prepare':q=elite();print(len(q),Counter(r['score'] for r in q));return
 if mode=='control':
  for i,z in enumerate(c):
   if z['mode']=='damage' and z['damage']==5:
    st,n,cut,w=complete(z,unpack(z['start']),5,50000,191);print(json.dumps([i,st,n,cut,w],separators=(',',':')),flush=True)
  return
 k,lim,step=map(int,sys.argv[2:5]);rows=read('elite.jsonl')
 for ix,z in enumerate(rows):
  if ix%step:continue
  cc=c[z['id']];st,n,cut,w=complete(cc,unpack(z['mask']),k,lim,192)
  print(json.dumps([ix,st,n,cut,w],separators=(',',':')),flush=True)
  if w:break
if __name__=='__main__':main()
