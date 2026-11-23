from search import *
rows=json.loads((r/'seeds.json').read_text())
refs=json.loads((r/'reference.json').read_text())
old=set()
for f in ('q9_all190_20261119.csv','q9_beam190_20261119.csv'):
 for z in csv.DictReader(open('/tmp/'+f)):
  p=list(map(int,z['vertices'].split()))
  if len(p)==191:old.add(key(p))
old189=set()
for f in ('q9_all190_20261119.csv','q9_beam190_20261119.csv'):
 for z in csv.DictReader(open('/tmp/'+f)):
  p=list(map(int,z['vertices'].split()))
  if len(p)==191:old189.update([key(p[:-1]),key(p[1:])])
def ascii_key(k):return ''.join(str(d) for d in k)
(r/'known190.txt').write_text(''.join(ascii_key(k)+'\n' for k in old))
a=[];b=[]
for l in (r/'chain-seeds.jsonl').open():
 _,n,_,_,p,span=json.loads(l)
 if n!=189:continue
 if key(p) not in old189:a.append((p,span))
 else:b.append((p,span))
rng=Random(6284);rng.shuffle(a);rng.shuffle(rows);items=a+[(p,rng.choice(ss)) for p,ss in rows]+b
with (r/'cores.txt').open('w') as fp:
 for p,(i,L) in items:print(i,L,*p,file=fp)
with (r/'controlcores.txt').open('w') as fp:
 for p in refs[:4]:print(78,9,*p[2:-2],file=fp)
print('fresh189_not_even_trimmed190',len(a),'others190_or189_with_private_factor',len(rows),'189_from_190_fragment',len(b))

