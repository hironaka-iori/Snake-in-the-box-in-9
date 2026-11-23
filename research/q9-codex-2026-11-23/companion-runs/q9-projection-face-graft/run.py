from pathlib import Path
from collections import Counter
from time import monotonic
import sys,json,random
from prep import verify
r=Path(__file__).resolve().parent
ws=Path('/Users/yichenzhan/Documents/ChatGPT/snake-in-the-box')
sys.path.insert(0,str(ws))
from search_q9_unordered_projection import solve
def combine(a,b,mask,v,flip=False):
 return {z for z in a if (z&mask)!=v}|{z^(256 if flip else 0) for z in b if (z&mask)==v}
def runctrl():
 output=[]
 for x in json.loads((r/'controls.json').read_text()):
  A=x['A'];B=x['B'];h=combine(A,B,x['mask'],x['value']);S={v%256 for v in h};assert S not in [{z%256 for z in A},{z%256 for z in B}]
  st,p=solve(h,191,50000)
  if p:
   verify(p);assert len(p)==192 and {z%256 for z in p}==S
  output.append([st,p]);print('control',st,len(p) if p else 0,flush=True)
 (r/'ctrl.json').write_text(json.dumps(output))
def run(tag,n,budget,sec,mode):
 inputs=[]
 for l in (r/'parents.pts').open():
  i,o,d,*p=map(int,l.split());inputs.append((i,p))
 rows=[list(map(int,l.split())) for l in (r/('exact.pts' if tag.startswith('exact') else 'grafts.pts')).read_text().splitlines() if len(l.split())==10];rng=random.Random(7412+mode);ix=list(range(len(rows)));rng.shuffle(ix)
 if mode==0:ix.sort(key=lambda i:(-rows[i][7],rows[i][6]//2))
 elif mode==1:ix.sort(key=lambda i:(-min(rows[i][4],rows[i][5]),rows[i][6]//3))
 elif mode==2:ix.sort(key=lambda i:abs(rows[i][8]-186))
 elif mode==3:ix=[i for i in ix if rows[i][7]]
 elif mode==4:ix=[i for i in ix if rows[i][6]!=0]
 done=set()
 if mode==5:done={json.loads(l)[0] for nm in ('first','all') for f in [r/(nm+'.jsonl')] if f.exists() for l in f.read_text().splitlines()}
 if mode==6:done={json.loads(l)[0] for nm in ('exact','exactrest') for f in [r/(nm+'.jsonl')] if f.exists() for l in f.read_text().splitlines()}
 ix=[i for i in ix if i not in done]
 counts=Counter();scores=Counter();t=monotonic();winners=[]
 with (r/(tag+'.jsonl')).open('w',1) as out:
  for i in ix[:n]:
   a,b,m,v,g,l,dist,ham,size,free=rows[i];pa,A=inputs[a];pb,B=inputs[b];assert pa!=pb
   s1={z%256 for z in A};s2={z%256 for z in B};h=combine(A,B,m,v);S={z%256 for z in h}
   assert S !=s1 and S!=s2 and len(S)==size and len(S-s1)==g and len(s1-S)==l
   flip=combine(A,B,m,v,True)
   if len(h^set(A))>len(flip^set(A)):h=flip
   st,p=solve(h,192,budget)
   if p:
    verify(p);assert len(p)==193 and {z%256 for z in p}==S;winners.append(i)
   counts[st]+=1;scores[(dist,ham)]+=1;print(json.dumps([i,a,b,m,v,st,p],separators=(',',':')),file=out)
   if p or monotonic()-t>=sec:break
 print(tag,dict(counts),'matched_and_hamiltonian',sum(k for (d,h),k in scores.items() if h),'grafts_available',len(rows),'winners',winners,flush=True)
if __name__=='__main__':
 if sys.argv[1]=='control':runctrl()
 else:run(sys.argv[1],*map(int,sys.argv[2:]))

