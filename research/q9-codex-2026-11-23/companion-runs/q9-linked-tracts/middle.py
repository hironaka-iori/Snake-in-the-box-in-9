from prep import *
rng=Random(1219345);classes={}
for l in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt'):
 p=list(map(int,l.split()))
 if len(p)==192:classes.setdefault(shape(p),p)
for x in csv.DictReader(open('/tmp/q9_all190_20261119.csv')):
 p=list(map(int,x['vertices'].split()));classes.setdefault(shape(p),p)
paths=list(classes.values());choices=[];buckets=defaultdict(list);forms=[]
for j,p in enumerate(paths):
 for ori,t in enumerate((p,p[::-1])):
  k=len(forms);forms.append((j,t))
  for l in range(rng.randrange(5),len(t)-11,5):
   dims=[(a^b).bit_length()-1 for a,b in zip(t[l:l+11],t[l+1:l+12])];labels=list(dict.fromkeys(dims));key=tuple(labels.index(d) for d in dims)
   if len(labels)>=5:buckets[key].append((k,l,labels))
seen=set()
with (r/'middles.pts').open('w') as f,(r/'middle_manifest.txt').open('w') as desc:
 pools=[q for q in buckets.values() if len(q)>=2]
 for trial in range(60000):
  group=rng.choice(pools);(u,i,labels),(v,j,labs)=rng.sample(group,2);pa,A=forms[u];pb,B=forms[v]
  if pa==pb:continue
  aleft=[x for x in range(9) if x not in labels];bleft=[x for x in range(9) if x not in labs]
  best=None;aset=set(A)
  for c in range(min(6,1 if not aleft else 6)):
   rng.shuffle(aleft);m=dict(zip(labs+bleft,labels+aleft));trans=[0]*512
   for n in range(1,512):trans[n]=trans[n&(n-1)]|(1<<m[(n&-n).bit_length()-1])
   off=A[i]^trans[B[j]];P=[off^trans[x] for x in B];ov=len(aset.intersection(P))
   if best is None or ov>best[0]:best=ov,P,tuple(m[k] for k in range(9)),off
  ov,P,perm,off=best
  if ov<85 or ov>188:continue
  identity=(u,v,perm,off)
  if identity in seen:continue
  seen.add(identity);print(*A,file=f);print(*P,file=f);print(pa,pb,i,j,ov,file=desc)
  if len(seen)>=6500:break
print('mapped_parent_pairs',len(seen))

