from prepare import *
from salvage import canon,word
from collections import Counter
def read(f):return [json.loads(s) for s in (D/f).read_text().splitlines()]
def topology(S,major,goal):
 adj={v:{w for w in S if (v^w).bit_count()==1} for v in S};h=Counter(len(b) for b in adj.values());ends=Counter(v.bit_count()%2 for v,z in adj.items() if len(z)==1);un=set(S);groups=0
 while un:
  todo=[un.pop()]
  for x in todo:
   fresh=un&adj[x];un-=fresh;todo.extend(fresh)
  groups+=1
 edges=sum(k*n for k,n in h.items())//2;cycles=edges-len(S)+groups
 desired=[1,1] if goal%2 else [2*int(i==major) for i in (0,1)]
 cost=9*sum((k-2)*v for k,v in h.items() if k>2)+7*h[0]+3*sum(abs(ends[i]-desired[i]) for i in (0,1))+5*(groups-1)+6*cycles
 return cost,groups,cycles,dict(h)
C=read('cases.jsonl');W=(R/'q8_catalogue_96_98.words').read_text().split();refs=(R/'q9_gap_generations/prior191.words').read_text().splitlines();bank={canon(w) for w in refs};sources={f:list(map(json.loads,(R/f).read_text().splitlines())) for f in {r['src'] for r in C}}
def check_set(i,S):
 c=C[i];assert len(S)==c['goal']+1 and unpack(c['anchor'])<=S<=unpack(c['allowed']);actual=Counter(v.bit_count()%2 for v in S)
 assert all(actual[k]==(c['goal']+1)//2+int(c['goal']%2==0 and c['majority']==k) for k in (0,1))
H={};report={};visited=set();refs_checked={}
for mode in ('damage','cold','warm','blend'):
 inputs=(D/(mode+'.in')).read_text().splitlines();recs=(D/(mode+'.log')).read_text().splitlines();assert len(inputs)==len(recs)
 starts=[];ends=[];count=Counter();profiles=Counter();pairs=hits=equal=0;classes=set();archive=[]
 for line,record in zip(inputs,recs):
  raw=list(map(int,line.split()));i,goal,ma=raw[:3];c=C[i];s=unpack(c['start']);f=unpack(c['anchor']);allow=unpack(c['allowed']);assert i not in visited;visited.add(i)
  rec=sources[c['src']][c['line']];p=walk(W[c['id']]);tr=c['trim'];assert rec['word']==W[c['id']] and rec['index']==c['id'] and rec['majority']==ma
  assert set(p[tr:len(p)-tr])==f and allow==f|{v for v in range(512) if v not in f and len(N[v]&f)<=2 and not any(w in f and len(N[w]&f)==2 for w in N[v])}
  probs=dict(rec['occupancy_permille']);assert raw[27:]==[probs.get(v,1000 if v in p else 125) for v in range(512)]
  assert all(sum(raw[offset+j]<<(64*j) for j in range(8))==int(c[key],16) for offset,key in [(3,'anchor'),(11,'allowed'),(19,'start')])
  check_set(i,s);x=record.split();tag=x[0];a=list(map(int,x[1:]));j,rep,it,initial,best,accepted,candidates,topocalls,shakes,g,cy=a[:11];mask=sum(n<<(64*k) for k,n in enumerate(a[11:19]));S=unpack(format(mask,'x'));H[i]=S
  assert i==j and rep==0 and it<=(120 if mode=='damage' else 240);check_set(i,S)
  raw_first=topology(s,ma,goal);raw_best=topology(S,ma,goal);assert (initial,best,g,cy)==(raw_first[0],raw_best[0],raw_best[1],raw_best[2])
  starts.append(initial);ends.append(best);pairs+=candidates;profiles[(g,cy,tuple(sorted(raw_best[3].items())),best)]+=1
  if mode in ('damage','warm','blend'):
   key=(c['id'],c['ref'])
   if key not in refs_checked:refs_checked[key]=set(align(refs[c['ref']],W[c['id']]))
   truth=refs_checked[key]
   if mode=='damage':assert len(s-truth)==c['damage'] and initial>0
   if mode=='warm':assert truth<s and len(s-truth)==1
  if tag=='FOUND':
   q=a[19:];assert S==set(q) and len(q)==goal+1 and valid(q) and best==0
   hits+=1;classes.add(canon(word(q)));count[c['damage']]+=1
   if mode=='damage':equal+=S==truth
  else:assert tag=='BEST' and len(a)==19 and best>0
 report[mode]=dict(seeds=len(inputs),max_steps=120 if mode=='damage' else 240,pairs=pairs,best=min(ends),start_range=[min(starts),max(starts)],hits=hits,hit_classes=len(classes),dmg_hits=count,exact_reference_recoveries=equal,close_profiles=[(str(k),v) for k,v in profiles.items() if k[-1]==min(ends)])
assert len(visited)==len(C)
elite=read('elite.jsonl');assert len({(r['mask'],C[r['id']]['anchor']) for r in elite})==len(elite)
for r in elite:assert H[r['id']]==unpack(r['mask'])
repair={}
for name,k in [('exactcontrol',3),('r2',2),('r3',3),('r4',4)]:
 ids=[int(l.split()[0]) for l in (D/(name+'.in')).read_text().splitlines()];lines=(D/(name+'.log')).read_text().splitlines();assert len(lines)==len(ids)
 stats=Counter();calls=[0]*3
 for ix,line in zip(ids,lines):
  a=line.split();assert int(a[0])==ix;st=a[1];stats[st]+=1
  calls=[u+int(v) for u,v in zip(calls,a[2:5])]
  if st=='FOUND':
   i=ix if name=='exactcontrol' else elite[ix]['id'];base=unpack(C[i]['start']) if name=='exactcontrol' else H[i];q=list(map(int,a[5:]));check_set(i,set(q));assert len(q)==C[i]['goal']+1 and valid(q) and 1<=len(base-set(q))<=k
  else:assert st=='EXHAUSTED' and len(a)==5
 repair[name]=dict(radius=k,domains=len(ids),results=stats,removal_sets=calls[0],linear_residues=calls[1],addition_leaves=calls[2])
for name,k,step in [('radius6',6,1),('radius15',15,5),('radius_control',5,0)]:
 ids=list(range(0,len(elite),step)) if step else [i for i,c in enumerate(C) if c['mode']=='damage' and c['damage']==5];lines=read(name+'.log');assert len(ids)==len(lines);st=Counter()
 for j,(i,status,conf,cuts,p) in zip(ids,lines):
  assert i==j;st[status]+=1
  if p:
   n=i if not step else elite[i]['id'];start=unpack(C[n]['start']) if not step else H[n];check_set(n,set(p));assert valid(p) and len(p)==C[n]['goal']+1 and len(start-set(p))<=k
 repair[name]=dict(radius=k,domains=len(ids),results=st)
sal=read('salvage.jsonl');cls=set();by=Counter();delta=set()
for r in sal:
 i=r['case'];p=r['vertices'];assert len(p)==192 and valid(p) and set(p)==H[i]-{r['removed']} and unpack(C[i]['anchor'])<=set(p)
 w=canon(word(p));assert w==r['canonical'] and (w in bank)==r['known'];cls.add(w);by[r['mode']]+=1
 if C[i]['ref'] is not None and w!=canon(refs[C[i]['ref']]):delta.add(w)
print(json.dumps(dict(lp_snapshots={src:len({r['line'] for r in C if r['src']==src}) for src in sources},distinct_donors=len(set(r['id'] for r in C)),known_reference_placements=len(refs_checked),input_and_best_sets_verified=len(C)*2,search=report,distinct_elites=len(elite),repair=repair,salvage=dict(valid=len(sal),classes=len(cls),new=len(cls-bank),different_from_input_classes=len(delta),modes=by)),indent=2))
