from families import *
data=[json.loads(l)[0] for l in (D/'families.jsonl').read_text().splitlines()]
seen={};index=[]
for i,word in enumerate(data):
 w=tuple(word);ids=[]
 for size in (26,32,38,44,49,54,59,64,69,74):
  if size>=len(w):continue
  for a in sorted({0,len(w)-size,(len(w)-size)//2,(len(w)-size)//3,2*(len(w)-size)//3}):
   sub=w[a:a+size];sg=sig(sub)
   if sg not in seen:seen[sg]=[len(seen),sub]
   ids.append([a,size,seen[sg][0]])
 index.append(ids)
with (D/'trims.in').open('w') as f:
 for i,w in seen.values():print(i,len(w),*w,file=f)
(D/'trims-index.jsonl').write_text(''.join(json.dumps(a,separators=(',',':'))+'\n' for a in index));print(len(seen))
