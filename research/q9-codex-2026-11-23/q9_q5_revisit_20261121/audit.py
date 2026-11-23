from prepare import *
import hashlib,collections
def read(f):return list(map(json.loads,(D/f).read_text().splitlines()))
def h(p):return ''.join(str((v^w).bit_length()-1) for v,w in zip(p,p[1:]))
def canon(w):
 def norm(x):
  d={};return ''.join(str(d.setdefault(a,len(d))) for a in x)
 return min(norm(w),norm(w[::-1]))
def val(p):
 assert len(set(p))==len(p) and all(0<=v<512 for v in p) and all((v^w).bit_count()==1 for v,w in zip(p,p[1:]))
 return [(i,j) for i,v in enumerate(p) for j in range(i+2,len(p)) if (v^p[j]).bit_count()==1]
words=(R/'q9_gap_generations/prior191.words').read_text().split();bank={canon(w) for w in words};P=list(map(path,words));assert len(P)==131 and all(len(p)==192 and not val(p) for p in P)
cases=read('cases.jsonl');C=read('controls.jsonl');res={}
def geo(r):
 p=P[r['r']];a=r['a'];f=set(r['f']);return {v for v in p if lay(v,a) not in f},{v for v in range(512) if lay(v,a) in f}
def validate(q,r):
 fixed,free=geo(r);assert fixed<=set(q)<=fixed|free and not val(q)
coverage=collections.Counter();vis=collections.Counter();domains=set();removed=[];visfree=[]
for r in cases:
 s=seq(P[r['r']],r['a']);f=set(r['f']);fixed,free=geo(r)
 assert len(s)==r['k'] and 20<=len(s)<=25 and any(s.count(x)>=2 for x in f)
 domains.add((frozenset(fixed),frozenset(free)));vis[len(s)]+=1;removed.append(192-len(fixed));visfree.append(sum(x in f for x in s));coverage[len(f)]+=1
base=read('mini.log');extra=read('cad.log')
assert [r[0] for r in base]==list(range(len(cases))) and {r[0] for r in extra}=={i for i,s,w in base if s=='UNKNOWN'}
st={i:s for i,s,w in base}
for i,t,w in base+extra:
 if w:validate(w,cases[i]);assert len(w)>=193
 if t!='UNKNOWN':st[i]=t
res['domains']=dict(systems=len(cases),distinct=len(domains),templates=len(set((r['r'],tuple(r['a'])) for r in cases)),sizes=coverage,segment_counts=vis,removed_vertices=[min(removed),max(removed)],removed_visits=[min(visfree),max(visfree)],mini=collections.Counter(x[1] for x in base),cad_on_unknown=collections.Counter(x[1] for x in extra),merged=collections.Counter(st.values()))
unique={}
for i,r in enumerate(cases):
 f,g=geo(r);key=(frozenset(f),frozenset(g));unique.setdefault(key,set()).add(st[i])
res['domains']['distinct_status']=collections.Counter('UNSAT' if 'UNSAT' in sts else 'FOUND' if 'FOUND' in sts else 'UNKNOWN' for sts in unique.values())
for mode in ('control','warm','partial'):
 out=read(mode+'.log');assert len(out)==len(C)
 checked=[]
 for j,st,w in out:
  c=C[j];a=c['a'];src=P[c['r']]
  if st=='FOUND':
   validate(w,c);assert len(w)==192 and norm(seq(w,a))!=norm(seq(src,a))
   checked.append(dict(id=j,old=len(seq(src,a)),new=len(seq(w,a)),changed_vertices=len(set(src)-set(w)),changed_ports=len(ports(src,a)^ports(w,a)),known_class=canon(h(w)) in bank))
 res[mode]=dict(states=collections.Counter(x[1] for x in out),controls=checked)
for mode in ('mix','mixwide'):
 rec=[list(map(int,s.split())) for s in (D/(mode+'.log')).read_text().splitlines()];starts={r[0]:r[2:] for r in (list(map(int,s.split())) for s in (D/'start.txt').read_text().splitlines())};assert len(rec)==len(starts) and set(starts)=={r[0] for r in rec}
 caps=[]
 for i,k,acc,diff,b,new,near,*q in rec:
  if q:
   assert not val(q) and len(q)-1==b and q!=starts[i];caps.append([b,canon(h(q)) in bank])
 res[mode]=dict(templates=len(rec),attempts_per_template=9000 if mode=='mix' else 36000,accepted=sum(r[2] for r in rec),alternate_clean_outputs_by_template=sum(r[3] for r in rec),max_alternate=max(r[4] for r in rec),max_alternate_different_order=max(r[5] for r in rec),verified_saved_191=sum(x[0]==191 for x in caps),saved_nonbank191=sum(x==[191,False] for x in caps))
near={};nearrows=[];reference=set(map(canon,(R/'q9_three_axis.in').read_text().splitlines()))
for s in (D/'near.txt').read_text().splitlines():
 i,b,n,*q=map(int,s.split());assert len(q)==n;ch=val(q);assert len(ch)==b
 near[i]={q[j]//32 for a in ch for j in a}
 nearrows.append([i,n-1,b,canon(h(q)) in reference]);assert n>=193
rep=read('repair.log');keys={(i,tuple(f)) for _,i,f,_,_ in rep}
wanted={(i,tuple(sorted(c|set(t)))) for i,c in near.items() for k in (0,1,2) for t in itertools.combinations(sorted(set(range(16))-c),k)};assert keys==wanted and len(rep)==len(keys)
for _,i,f,st,w in rep:
 if w:assert len(w)>=193 and not val(w)
deep=read('repairdeep.log');assert {a[0] for a in deep}=={a[0] for a in rep if a[3]=='UNKNOWN'}
for i,r,f,st,w in deep:
 assert rep[i][:3]==[i,r,f]
 if w:assert len(w)>=193 and not val(w)
combined={x[0]:x[3] for x in rep}
for i,r,f,st,w in deep:combined[i]=st
res['near']=nearrows;res['repair']=dict(jobs=len(rep),first=collections.Counter(x[3] for x in rep),retry=collections.Counter(x[3] for x in deep),combined=collections.Counter(combined.values()))
print(json.dumps(res,indent=2))
