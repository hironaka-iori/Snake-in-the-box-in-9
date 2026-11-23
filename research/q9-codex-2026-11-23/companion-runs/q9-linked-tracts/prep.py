from pathlib import Path
from itertools import combinations
from collections import defaultdict
from random import Random
import gzip,csv,json
r=Path(__file__).resolve().parent;ws=Path('/Users/yichenzhan/Documents/ChatGPT/snake-in-the-box')
def ok(p):
 return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((v^p[j]).bit_count()==1)==(j-i==1) for i,v in enumerate(p) for j in range(i+1,len(p)))
def orient(p):
 m={};out=[0]
 for a,b in zip(p,p[1:]):out.append(out[-1]^(1<<m.setdefault(a^b,len(m))))
 return out
def shape(p):return min(tuple(orient(p)),tuple(orient(p[::-1])))
def dump(f,ls):f.write_text(''.join(' '.join(map(str,l))+'\n' for l in ls))
def main():
 classes={}
 for s in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt'):
  p=list(map(int,s.split()))
  if len(p)==192:classes.setdefault(shape(p),p)
 n191=len(classes)
 for x in csv.DictReader(open('/tmp/q9_all190_20261119.csv')):
  p=list(map(int,x['vertices'].split()));classes.setdefault(shape(p),p)
 pths=list(classes.values());bylens=defaultdict(int);ctrl=[];meta=[]
 for p in pths:
  assert ok(p)
  if len(p)!=192 or len(ctrl)>=6:continue
  alt={i:p[i]^p[i-1]^p[i+1] for i in range(7,len(p)-7)};flips=[i for i,x in alt.items() if x not in p and all((x^v).bit_count()!=1 for j,v in enumerate(p) if abs(j-i)!=1)]
  for i,j in combinations(flips,2):
   if j-i<18:continue
   a=p[:];a[i]=alt[i];a[j]=alt[j];a=a[1:-1];b=p[3:-3]
   if not ok(a) or not ok(b):continue
   ci=i-1;cj=j-1;ctrl.append((a,b));meta.append([ci,cj]);break
 dump(r/'ctrl.pts',[q for pair in ctrl for q in pair]);dump(r/'ctrlmeta.txt',meta)
 orienteds=[(j,orient(q)) for j,p in enumerate(pths) for q in (p,p[::-1])]
 rng=Random(173913);anchors=[]
 # Index parent pairs by two shared ordered local words/coincident positions in their normalized coordinates.
 feat=defaultdict(list);vals=[set(p) for _,p in orienteds]
 for k,(j,p) in enumerate(orienteds):
  for t in range(0,len(p)-4,4):feat[(p[t],p[t+2],p[t+4])].append(k)
 for ia,(pa,p) in enumerate(orienteds):
  candidates=set()
  for t in range(0,len(p)-4,4):
   bucket=feat[p[t],p[t+2],p[t+4]];candidates.update(rng.sample(bucket,min(12,len(bucket))))
  ranks=[]
  for ib in candidates:
   pb,q=orienteds[ib]
   if pa==pb:continue
   overlap=len(vals[ia]&vals[ib]);ranks.append((overlap,ib))
  for target in (105,135,156,173):
   if ranks:anchors.append((ia,min(ranks,key=lambda pair:abs(pair[0]-target))[1]))
 rng.shuffle(anchors);done=set();out=[]
 for i,j in anchors:
  if (i,j) in done:continue
  done.add((i,j));out.append((orienteds[i][1],orienteds[j][1]))
  if len(out)>=1600:break
 dump(r/'pairs.pts',[p for pair in out for p in pair]);print('classes',len(classes),'191 classes',n191,'control',len(ctrl),'real ordered pairs',len(out))
if __name__=='__main__':main()

