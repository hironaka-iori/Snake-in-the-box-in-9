from prep import *
from collections import Counter
from itertools import combinations
from hashlib import sha256
def bits(ls):return sum(1<<x for x in set(ls))
def key(p):return min(word(p),word(p[::-1]))
bank=[];ids=[]
for l in (r/'parents.pts').open():
 i,o,d,*p=map(int,l.split());ids.append(i);bank.append(bits(z%256 for z in p))
parents=set(bank);families=[];st={};seen=set();dims=Counter();matches=ham=0
for g,nm in enumerate(('grafts','exact')):
 rows=[]
 for l in (r/(nm+'.pts')).open():
  a,b,m,v,ga,lo,dist,hamilt,n,free=map(int,l.split());F=bits(x for x in range(256) if (x&m)==v)
  A,B=bank[a],bank[b];S=(A&~F)|(B&F)
  assert ids[a]!=ids[b] and A!=B and S not in parents and ga==(S&~A).bit_count() and lo==(A&~S).bit_count() and ga and lo and n==S.bit_count()
  assert (S&F)==(B&F) and (S&~F)==(A&~F)
  if S not in seen:dims[8-m.bit_count()]+=1
  seen.add(S);rows.append(S);matches+=not dist;ham+=hamilt
 assert len(rows)==len(set(rows));families.append(rows)
for name,g in [('first',0),('all',0),('exactmain',1)]:
 for l in (r/(name+'.jsonl')).open():
  i,a,b,m,v,res,p=json.loads(l);assert (g,i) not in st
  if p:verify(p);assert len(p)==193 and bits(x%256 for x in p)==families[g][i]
  st[g,i]=res
for l in (r/'retry.jsonl').open():
 g,i,res,p=json.loads(l);assert st[g,i]=='UNKNOWN'
 if p:verify(p);assert len(p)==193
 st[g,i]=res
assert len(st)==sum(map(len,families))
byshape={}
for (g,i),v in st.items():
 S=families[g][i]
 if S in byshape:assert byshape[S]==v
 byshape[S]=v
positive=json.loads((r/'ctrl.json').read_text())
for (st0,w),c in zip(positive,json.loads((r/'controls.json').read_text())):
 verify(w);assert len(w)==192 and st0=='FOUND'
 verify(c['A']);verify(c['B']);m=c['mask'];v=c['value'];S={x%256 for x in c['A'] if (x&m)!=v}|{x%256 for x in c['B'] if (x&m)==v};assert S=={x%256 for x in w}
real={};control_output=[]
for l in (r/'rank191.jsonl').open():
 g,i,cost,status,label,p=json.loads(l)
 if p:
  verify(p);assert len(p)==192 and bits(x%256 for x in p)==families[g][i]
  real[key(p)]=p
  control_output.append(dict(group=g,row=i,classification=label,vertices=p))
(r/'natural191.json').write_text(json.dumps(control_output,separators=(',',':'))+'\n')
known={key(q) for l in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt') if len(q:=list(map(int,l.split())))==192}
info={'source_raw':len(parents),'source_parent_classes':len(set(ids)),'candidate_rows':sum(map(len,families)),'distinct_candidate_sets':len(seen),'actual_target_by_row':dict(Counter(st.values())),'actual_target_by_distinct_set':dict(Counter(byshape.values())),'matching_Q8_path_boundaries_rows':matches,'inherited_Q8_Hamiltonian_rows':ham,'face_dimensions_distinct':dict(dims),'truncation_191_controls':len(positive),'natural_191_hits':len(control_output),'natural_191_classes':len(real),'natural_191_classes_outside_131':len(real.keys()-known),'natural_191_tested_statuses':dict(Counter(json.loads(l)[3] for l in (r/'rank191.jsonl').open())),'spectrum':(r/'spectrum_all.log').read_text().strip()}
bythreshold={}
for g in (0,1):
 f=r/f'ge{g}.jsonl';latest={json.loads(l)[0]:json.loads(l)[1:] for l in f.open()}
 for l in (r/f'ge{g}retry.jsonl').open():
  i,res,p=json.loads(l);assert latest[i][0]=='UNKNOWN';latest[i]=[res,p]
 for i,(res,p) in latest.items():
  S=families[g][i];assert S not in bythreshold
  if p:verify(p);assert len(p)>=193 and bits(x%256 for x in p)==S
  bythreshold[S]=res
assert set(bythreshold)==set(byshape)
info['at_least_192_final_by_distinct_set']=dict(Counter(bythreshold.values()))
for S,v in bythreshold.items():
 if v=='PROJECTION':
  occ={x for x in range(256) if S>>x&1};sizes=[]
  while occ:
   comp=[occ.pop()]
   for u in comp:
    for d in range(8):
     v=u^(1<<d)
     if v in occ:occ.remove(v);comp.append(v)
   sizes.append(len(comp))
  info['rejected_projection_connected_components']=sizes
scores=Counter(info['natural_191_tested_statuses'])
for l in (r/'retry191.jsonl').open():
 g,i,score,status,label,p=json.loads(l);scores['UNKNOWN']-=1;scores[status]+=1
 if p:verify(p);assert len(p)==192
info['natural_191_statuses_after_retry']=dict(scores)
(r/'audit.json').write_text(json.dumps(info,indent=2)+'\n');print(info)

