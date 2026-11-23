from search import *
def main():
 src=json.loads((r/'seeds.json').read_text());rng=Random(471195);jobs=[]
 for idx,(p,ss) in enumerate(src):
  if len(p)!=191:continue
  for reverse in (0,1):
   q=p[::-1] if reverse else p;used=set(q)
   for d in range(9):
    y=q[-1]^(1<<d)
    if y in used:continue
    coll=[i for i,x in enumerate(q[:-1]) if (x^y).bit_count()==1]
    if len(coll)!=1 or coll[0] in (0,len(q)-2):continue
    jobs.append((idx,reverse,d,coll[0]))
 print('one_chord_templates',len(jobs),flush=True);refs={key(p) for p in json.loads((r/'reference.json').read_text())};hits=Counter();start=monotonic()
 with (r/'cascade.jsonl').open('w',1) as f:
  for turn in range(9):
   rng.shuffle(jobs)
   for idx,reverse,d,i in jobs:
    q,ss=src[idx];p=q[::-1] if reverse else q;used=set(p);y=p[-1]^(1<<d);x=p[i];alt=p[i-1]^p[i+1]^x
    force={y,p[-1]};dead={x};possible=set();blocked=set()
    if turn%3:
     if alt in used or (alt^y).bit_count()<2:continue
     force.update((alt,p[i-1],p[i+1]));hit={v for v in used if (v^alt).bit_count()==1}-force
     dead.update(hit)
     for at in hit:
      j=p.index(at)
      if 0<j<len(p)-1:
       z=p[j-1]^p[j+1]^at
       if z not in used:
        possible.add(z);blocked.update(v for v in used if (z^v).bit_count()==1)
    else:
     hit={v for v in used if (v^alt).bit_count()==1}
     possible.update((alt,p[i-1],p[i+1]));blocked.update(hit)
    if force&dead:continue
    spans=[(t,L) for t,L in ss if not dead.intersection(q[t:t+L])]
    if not spans:continue
    t,L=rng.choice(spans);anchor=set(q[t:t+L]);cols,syn=code(rng);release={syn[v] for v in dead|possible|blocked}
    for k in (i-2,i-1,i+1,i+2):
     if 0<=k<len(p):release.add(syn[p[k]])
    for j in rng.sample(range(16),2):release.add(j)
    if len(release)>12:continue
    free={v for v in range(512) if syn[v] in release};fixed=(used-free)|anchor|force
    if fixed&dead:continue
    allowed=(free|fixed)-dead;goal=191
    st,w=search(fixed,used,goal,6500,allowed=allowed,at_least=True);hits[st]+=1
    if w:
     assert valid(w) and (len(w)>192 or key(w) not in refs);ext=extend(w);assert all(valid(a) for a in ext);(r/'cascade-positive.json').write_text(json.dumps({'vertices':w,'extensions':ext}))
    print(json.dumps([turn,idx,reverse,d,i,cols,sorted(release),t,L,sorted(dead),sorted(force),st,w],separators=(',',':')),file=f)
    if w or monotonic()-start>47:break
   if w or monotonic()-start>47:break
 print(dict(hits))
if __name__=='__main__':main()

