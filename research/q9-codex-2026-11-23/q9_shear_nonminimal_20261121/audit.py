from families import *
from collections import Counter
def read(n):return [json.loads(s) for s in (D/n).read_text().splitlines()]
def valid(w):
 assert 0<=min(w)<=max(w)<512 and len(set(w))==len(w)
 assert all(((x^y).bit_count()==1)==(i+1==j) for i,x in enumerate(w) for j,y in enumerate(w) if j>i)
def support(q,c,L,R0,l,r,det,target):
 valid(q);assert len(q)==target+1 and q[l]==c[0] and q[-1-r]==c[-1] and (q[0]^c[0]).bit_count()==l and (q[-1]^c[-1]).bit_count()==r and not((q[0]^c[0])&~L or (q[-1]^c[-1])&~R0)
 idx=[q.index(v) for v in c];assert all(y-x==(a^b).bit_count()+det.get(i,0) for i,(a,b,x,y) in enumerate(zip(c,c[1:],idx,idx[1:])))
W=(R/'q9_gap_generations/prior191.words').read_text().splitlines();parents=[reconstruct(tuple(1<<int(k) for k in w)) for w in W];assert len(parents)==131
for q in parents:valid(q);assert len(q)==192
log=read('relax.log');old=read('cases.jsonl');src=cases();assert len(src)==332 and len(old)==len(log)==115
for i,(j,st,solutions) in enumerate(log):
 assert j==i and solutions==[] and all(s=='UNSAT' and count==0 for k,s,count,conf in st)
 for z in old[i]['equiv']:assert key(old[i])==key(src[z])
assert sorted(z for r in old for z in r['equiv'])==list(range(332))
new={};counts=Counter()
for f in sorted(D.glob('*.work')):
 name=f.stem
 if not name[1:4].isdigit():continue
 recs=(D/(name+'.log')).read_text().splitlines();assert len(recs)==131
 for ix,line in enumerate(f.read_text().splitlines()):
  row,d,t,a,j,L,R0,rem,np,k,*v=map(int,line.split());b=v[:k];p=v[k:];q=[u^(t if u>>d&1 else 0) for u in parents[row]]
  assert p==q[a:j+1] and L==(q[a]^q[a-1] if a else 0) and R0==(q[j]^q[j+1] if j<191 else 0)
  assert rem+sum(m.bit_count() for m in steps(p))==int(name[1:4]) and k<=2 and all(steps(p)[z].bit_count()>1 for z in b)
  new[name,ix]=(p,L,R0,rem);counts[name]+=1
families=read('families.jsonl');assert len(families)==2277 and len(new)==sum(len(r) for w,r in families)
assert {(f,i) for w,r in families for f,i in r}==new.keys()
for w,refs in families:
 for f,i in refs:assert sig(tuple(w))==sig(steps(new[f,i][0]))
rows=read('allrelax.log');known=set()
for i,st,*aux in rows:
 w=tuple(families[i][0])
 if st=='UNSAT':
  small=aux[1];assert any(tuple(small)==w[k:k+len(small)] for k in range(len(w)-len(small)+1));known.add(i)
 if st=='CONTAINS':
  j,n,other=aux[0];assert rows[other][1]=='UNSAT' and sig(tuple(rows[other][-1]))==sig(w[j:j+n]);known.add(i)
assert len(rows)==2277
def rs(name):return [list(map(int,l.split())) for l in (D/name).read_text().splitlines()]
for group in ['routes.log','routes2.log']:
 for i,s,ng,nodes in rs(group):
  if not s:known.add(i)
trims={i for i,s,ng,n in rs('trims.log') if not s};inputs={a[0]:tuple(a[2:]) for a in rs('trims.in')}
for i,ops in enumerate(read('trims-index.jsonl')):
 for j,n,k in ops:
  if k in trims:assert sig(tuple(families[i][0][j:j+n]))==sig(inputs[k]);known.add(i);break
pre=len(known);un=set(range(2277))-known;extra_modes={}
for n in ('final94','strong'):
 out=read(n+'.log');assert {q[0] for q in out}==un;extra_modes[n]=Counter(q[1] for q in out)
 for i,st,conf,which in out:
  if st=='UNSAT':known.add(i)
  if st=='SAT':assert which
controls=read('directcontrol.log');second=read('control2.log')
longlog=(D/'long.log').read_text().splitlines();lst=longlog[-1].split();assert lst[0]=='FOUND'
go,row,d,t,a,j,ix,e,nt,nf=map(int,lst[1:11]);c=[u^(t if u>>d&1 else 0) for u in parents[row][a:j+1]]
assert [int(s.split()[1]) for s in longlog[:-1]]==list(range(192,go,-1))
support(list(map(int,lst[11:])),c,0,0,0,0,{ix-a:e},go);assert second[2][0]=='FOUND';support(second[2][1],c,0,0,0,0,{ix-a:e},go)
for j,ctl in enumerate(controls):
 row,d,t,a,b,L,R0,rem,np,*p=map(int,(OLD/'control.work').read_text().splitlines()[ctl['ix']].split())
 det={int(k):v for k,v in ctl['det'].items()};target=31+sum(det.values());assert second[j][0]=='FOUND';support(ctl['w'],p,L,R0,ctl['l'],ctl['r'],det,target);support(second[j][1],p,L,R0,ctl['l'],ctl['r'],det,target)
endpoint=read('ends.log');left={(f,k) for i in range(len(families)) if i not in known for f,k in families[i][1]};endpoint_states={}
for ix,st,conf,det,refs in endpoint:
 sigs=set()
 for f,k in refs:
  p,L,R0,rem=new[f,k];sigs.add((key(dict(p=p,L=L,R=R0)),rem,1 if f[1:4]=='190' else 2));assert (f,k) in left and (f,k) not in endpoint_states
  endpoint_states[f,k]=st
 assert len(sigs)==1 and (st!='SAT' or len(det) in (1,2))
assert set(endpoint_states)==left
summary={}
for name in ['direct','wide']:
 cases_in=read(name+'.jsonl');outputs=read(name+'.log');assert len(cases_in)==len(outputs)
 stcount=Counter();hist=Counter();nc=Counter();sts={}
 for i,(rc,out) in enumerate(zip(cases_in,outputs)):
  if name=='direct':c=rc;ds=c['det'];l=c['l']
  else:fi,c,ds,l=rc
  det={int(k):v for k,v in ds.items()};p,L,R0,rem=new[c['label'],c['ix']];assert c['p']==p and len(det) in (1,2) and set(det.values())<={2,4} and all((p[z]^p[z+1]).bit_count()>1 for z in det)
  assert int(c['label'][1:4])+sum(det.values())==192 and 0<=l<=max(0,L.bit_count()-1) and 0<=rem-l<=max(0,R0.bit_count()-1)
  nth,*_,status,w=out;assert nth==i
  if w:support(w,p,L,R0,l,rem-l,det,192)
  stcount[status]+=1;sts[i]=status;hist[sum(det.values())]+=1;nc[len(det)]+=1
 if name=='wide':
  retry=read('retrywide.log');assert {q[0] for q in retry}=={i for i,s in sts.items() if s=='UNKNOWN'}
  for i,fc,st,w in retry:
   if w:
    fi,c,ds,l=cases_in[i];support(w,c['p'],c['L'],c['R'],l,c['rem']-l,{int(k):v for k,v in ds.items()},192)
   sts[i]=st
 if name=='wide':
  final=read('last40.log');assert {q[0] for q in final}=={i for i,s in sts.items() if s=='UNKNOWN'}
  for i,fc,st,w in final:
   if w:
    fi,c,ds,l=cases_in[i];support(w,c['p'],c['L'],c['R'],l,c['rem']-l,{int(k):v for k,v in ds.items()},192)
   sts[i]=st
 summary[name]=dict(cases=len(cases_in),gains=hist,detours=nc,first=stcount,combined=Counter(sts.values()))
print(json.dumps(dict(old_actual_cores=len(src),old_classes=len(old),old_native_second_verification=Counter(z[1] for z in rs('oldroute.log')),fresh_kept_by_input=counts,retained=len(new),new_core_classes=len(families),first_excluded=pre,deep=extra_modes,all_excluded=len(known),open_classes=sorted(set(range(2277))-known),excluded_window_count=sum(len(refs) for i,(w,refs) in enumerate(families) if i in known),endpoint_checked_classes=len(endpoint),endpoint_labelled_states=Counter(endpoint_states.values()),final_unexcluded_windows=sum(v!='UNSAT' for v in endpoint_states.values()),positive=[35,37,go],targets=summary),indent=2))
