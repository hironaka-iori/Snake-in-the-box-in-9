import json,math,random
from collections import defaultdict
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent
N=[{v^(1<<d) for d in range(9)} for v in range(512)]
def walk(w):
 p=[0]
 for c in w:p.append(p[-1]^(1<<int(c)))
 return p
def valid(p):return len(set(p))==len(p) and all(((u^v).bit_count()==1)==(j==i+1) for j,v in enumerate(p) for i,u in enumerate(p[:j]))
def align(src,word):
 for s in (src,src[::-1]):
  for a in range(len(s)-len(word)+1):
   chunk=s[a:a+len(word)];f=dict(zip(chunk,word))
   if len(f)!=8 or len(set(f.values()))!=8 or any(f[c]!=d for c,d in zip(chunk,word)):continue
   f[(set('012345678')-set(f)).pop()]='8'
   p=walk(''.join(f[c] for c in s));off=p[a];p=[v^off for v in p];assert p[a:a+len(word)+1]==walk(word) and valid(p);return p
def mask(s):return format(sum(1<<v for v in s),'x')
def unpack(s):return {v for v in range(512) if int(s,16)>>v&1}
def emit():
 W=(R/'q8_catalogue_96_98.words').read_text().split();refs=(R/'q9_gap_generations/prior191.words').read_text().split();rng=random.Random(7193521)
 sources=['q9_facet_bank_primal.jsonl','q9_facet_191_donors_four.jsonl'];special={43,44,464,472,576};seeds=defaultdict(list)
 for ix in sorted(special):
  for j,s in enumerate(refs):
   q=align(s,W[ix])
   if q:seeds[ix].append((j,q))
 assert all(len(seeds[ix])==5 for ix in special)
 records=[]
 for src in sources:
  snapshot=52 if src==sources[0] else 10
  for j,line in enumerate((R/src).read_text().splitlines()[:snapshot]):
   c=json.loads(line)
   if 'occupancy_permille' in c:records.append((src,j,c))
 def add(c,src,line,goal,trim,mode,reference=None,damage=0):
  ix=c['index'];maj=c['majority'];p=walk(c['word']);fix=set(p[trim:len(p)-trim]);saturated={x for x in fix if len(N[x]&fix)==2}
  allowed=fix|{v for v in range(512) if v not in fix and len(N[v]&fix)<=2 and not N[v]&saturated}
  probs=dict(c['occupancy_permille']);prior=[probs.get(v,1000 if v in p else 125) for v in range(512)]
  need=[(goal+1)//2+(goal%2==0 and col==maj) for col in (0,1)]
  refid=None
  if reference:refid,q=reference;truth=set(q)
  if mode in ('warm','damage'):
   s=set(truth)
   if mode=='warm':
    cand=sorted(x for x in allowed-s if x.bit_count()%2==maj)
    # Geometric cost of the added vertex, with the LP breaking ties.
    def merit(x):
     near=N[x]&s;return sum(len(N[y]&s)==2 for y in near)*6+abs(len(near)-2)*3-prior[x]/1300+rng.random()*.8
    s.add(min(cand,key=merit))
   else:
    removed=[]
    for k in range(damage):
     u=rng.choice(sorted(s-fix));s.remove(u);removed.append(u)
    for u in removed:
     cand=sorted(v for v in allowed-s-truth if (v^u).bit_count()%2==0)
     near=[v for v in cand if (v^u).bit_count()==2]
     s.add(rng.choice(near or cand))
    assert len(s^truth)==2*damage and any(len(N[v]&s)>2 or not(N[v]&s) for v in s)
  else:
   # Per-colour weighted sampling without replacement; no reference points enter the cold mode.
   s=set(fix)
   for col,k in enumerate(need):
    free=[v for v in allowed-fix if v.bit_count()%2==col]
    def rank(v):
     prob=prior[v]/1000
     if mode=='blend':prob=.77*(v in truth)+.23*prob
     u=rng.random();return math.log((prob+.03)/(1.03-prob))-.75*math.log(-math.log(u))
    free.sort(key=rank,reverse=True);s.update(free[:k-sum(v.bit_count()%2==col for v in fix)])
  assert fix<=s<=allowed and len(s)==goal+1 and [sum(v.bit_count()%2==col for v in s) for col in (0,1)]==need
  spec=dict(src=src,line=line,id=ix,majority=maj,goal=goal,trim=trim,mode=mode,ref=refid,damage=damage,anchor=mask(fix),allowed=mask(allowed),start=mask(s))
  fs.append((spec,prior))
 fs=[]
 for src,line,c in records:
  ix,maj=c['index'],c['majority']
  if src==sources[1]:
   for trim in (0,3,8,14):
    for ref in seeds[ix]:
     for mode in ('warm','blend'):add(c,src,line,192,trim,mode,ref)
   if maj==0:
    for j,ref in enumerate(seeds[ix]):
     for damage in (1,3,5):
      # Retry generation if the specified changes happen to leave degrees already feasible.
      for tries in range(50):
       try:add(c,src,line,191,0 if j%2==0 else 5,'damage',ref,damage);break
       except AssertionError:
        if tries==49:raise
  for trim in (0,4,10):
   add(c,src,line,192,trim,'cold')
   if trim and c['bound_scaled']>=193*c['scale']:add(c,src,line,192,trim,'cold')
 (D/'cases.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r,_ in fs))
 for name in ('damage','warm','cold','blend'):
  with (D/(name+'.in')).open('w') as f:
   for j,(r,prior) in enumerate(fs):
    if r['mode']!=name:continue
    z=[j,r['goal'],r['majority']]
    for k in ('anchor','allowed','start'):
     b=int(r[k],16);z.extend((b>>(64*i))%(1<<64) for i in range(8))
    print(*z,*prior,file=f)
 print(len(records),len(fs),[(i,len(seeds[i])) for i in special])
if __name__=='__main__':emit()
