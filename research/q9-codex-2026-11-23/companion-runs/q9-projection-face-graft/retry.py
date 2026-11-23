from run import *
bank=[list(map(int,l.split()))[3:] for l in (r/'parents.pts').open()]
files={'first':0,'all':0,'exactmain':1};counts=Counter()
with (r/'retry.jsonl').open('w',1) as out:
 for name,g in files.items():
  for line in (r/(name+'.jsonl')).open():
   i,a,b,m,v,st,p=json.loads(line)
   if st!='UNKNOWN':continue
   h=combine(bank[a],bank[b],m,v);st,p=solve(h,192,160000)
   if p:verify(p);assert len(p)==193
   counts[st]+=1;print(json.dumps([g,i,st,p]),file=out)
print(dict(counts))

