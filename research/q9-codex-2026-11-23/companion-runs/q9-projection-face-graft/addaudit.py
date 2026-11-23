from pathlib import Path
r=Path(__file__).resolve().parent;p=r/'audit.py';s=p.read_text()
key="(r/'audit.json').write_text"
pos=s.index(key)
s=s[:pos]+'''bythreshold={}
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
'''+s[pos:];p.write_text(s)

