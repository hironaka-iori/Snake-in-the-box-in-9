from search import *
def task(tag,secs,limit):
 refs={key(p) for p in json.loads((r/'reference.json').read_text())};sources=json.loads((r/'seeds.json').read_text());orig=set()
 for f in ('q9_all190_20261119.csv','q9_beam190_20261119.csv','q9_nonlocal189_seeds19.csv'):
  for row in csv.DictReader(open('/tmp/'+f)):
   p=list(map(int,row['vertices'].split()));orig.add(key(p))
 visited=set(orig);discovered=[];rng=Random(1827712);c=Counter();promote=[];start=monotonic()
 with (r/(tag+'.jsonl')).open('w',1) as log,(r/(tag+'-seeds.jsonl')).open('w',1) as out:
  for z in range(limit):
   borrowed=bool(discovered) and rng.random()<.65
   if promote:idx=promote.pop();p,spans=discovered[idx];borrowed=True;must=True
   else:
    must=False;idx=rng.randrange(len(discovered) if borrowed else len(sources));p,spans=(discovered if borrowed else sources)[idx]
   cols,syn=code(rng);inst=model(rng,p,spans,7,syn,rng.choice([0,1,1,2]))
   if not inst:continue
   _,_,old,span,force=inst;t,L=span;anchor=p[t:t+L];used=set(p);force=set(force)
   # The even and odd Hamming-parity sides get separately selected syndrome classes.
   by=[set(),set()]
   for v in force-used:
    for x in used:
     if (v^x).bit_count()==1:by[x.bit_count()%2].add(syn[x])
   for j,b in enumerate(by):
    size=rng.choice([5,6,7,8,9]);b.update(rng.sample([i for i in range(16) if i not in b],max(0,size-len(b))))
   free={x for x in range(512) if syn[x] in by[x.bit_count()%2]};F=(used-free)|set(anchor)|force;allowed=F|free
   goal=191 if must or z%5 in (0,1) else 190 if z%5 in (2,3) else 189
   st,w=search(F,used,goal,4500 if goal==191 else 1700,known=None if goal==191 else visited,allowed=allowed,at_least=goal==191);c[goal,st]+=1
   if w:
    assert valid(w) and F<=set(w)<=allowed;K=key(w)
    if len(w)>=192:
     assert K not in refs or len(w)>192
     ext=extend(w);assert all(valid(a) for a in ext)
     (r/(tag+'-positive.json')).write_text(json.dumps({'parent':[borrowed,idx],'vertices':w,'extensions':ext}));print(json.dumps([z,int(borrowed),idx,goal,st,len(w)-1]),file=log);break
    assert K not in visited;visited.add(K)
    if w.index(anchor[0])>w.index(anchor[-1]):anchor=anchor[::-1]
    l=w.index(anchor[0]);assert w[l:l+len(anchor)]==anchor
    discovered.append((w,[[l,len(anchor)]]));k=len(discovered)-1;promote.extend([k,k] if goal==190 else [k])
    print(json.dumps([k,goal,idx,borrowed,w,[l,len(anchor)]],separators=(',',':')),file=out)
   print(json.dumps([z,int(borrowed),idx,goal,st,len(w)-1 if w else None]),file=log)
   if monotonic()-start>=secs:break
 print('by_goal_status',dict(c),'distinct_unseen_intermediates',len(discovered))
if __name__=='__main__':task(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]))

