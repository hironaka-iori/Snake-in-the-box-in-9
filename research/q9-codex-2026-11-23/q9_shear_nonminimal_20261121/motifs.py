from families import *
def get():
 data=[json.loads(s) for s in (D/'families.jsonl').read_text().splitlines()];bank=collections.defaultdict(dict);excluded=set();proof=[]
 def add(w,k):
  w=tuple(w);bank[len(w)].setdefault(sig(w),k)
 ts=[list(map(int,l.split())) for l in (D/'trims.in').read_text().splitlines()]
 for l in (D/'trims.log').read_text().splitlines():
  i,st,ng,n=map(int,l.split())
  if st==0:add(ts[i][2:],['trim',i])
 old=[json.loads(s) for s in (D/'cases.jsonl').read_text().splitlines()]
 for i,c in enumerate(old):add(steps(c['p']),['old',i])
 for n in ('allrelax','final94','strong'):
  for l in (D/(n+'.log')).read_text().splitlines():
   i,st,*aux=json.loads(l)
   if st=='UNSAT' and n=='allrelax':add(aux[-1],['short',i])
   if st in ('UNSAT','CONTAINS'):add(data[i][0],[n,i]);excluded.add(i)
 for n in ('routes','routes2'):
  for l in (D/(n+'.log')).read_text().splitlines():
   i,st,ng,k=map(int,l.split())
   if st==0:add(data[i][0],[n,i]);excluded.add(i)
 for i,(w,_) in enumerate(data):
  if i in excluded:continue
  w=tuple(w);found=None
  for n,table in bank.items():
   for j in range(len(w)-n+1):
    sg=sig(w[j:j+n])
    if sg in table:found=[j,n,table[sg]];break
   if found:break
  if found:excluded.add(i);proof.append([i,found])
 return sorted(set(range(len(data)))-excluded),proof
if __name__=='__main__':
 u,p=get();(D/'motif.json').write_text(json.dumps(dict(open=u,links=p)));print(len(u),p[:4])
