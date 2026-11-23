from upper import *
rows=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
for j,r in enumerate(json.loads((D/'controls.json').read_text())):rows.insert(0,{'lower':r['lower'],'id':-r['ref']})
for r in rows:
 remaining=set(r['lower']);out=[]
 while remaining:
  q=[min(x for x in remaining if len(NB[x]&remaining)==1)];remaining.remove(q[0])
  while s:=NB[q[-1]]&remaining:
   x,=s;q.append(x);remaining.remove(x)
  out.append(q)
 if len(out)<2:continue
 print(r['id'],len(out),*(str(len(q))+' '+' '.join(map(str,q)) for q in out))
