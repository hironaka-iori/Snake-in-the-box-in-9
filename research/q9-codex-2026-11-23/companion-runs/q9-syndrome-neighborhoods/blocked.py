from search import *
class Seen(set):
 def __init__(self,items):super().__init__(items);self.blocked=0
 def __contains__(self,k):
  result=super().__contains__(k)
  if result:self.blocked+=1
  return result
def ctrl(refs):
 p=refs[0];pre=p[:-1];rng=Random(7773);cols,syn=code(rng);R={syn[v] for v in [p[-1],p[-4],p[23],p[67],p[150]]};free={x for x in range(512) if syn[x] in R};fixed=set(pre)-free
 known={key(q) for q in refs};output=[]
 for skip in (True,False):
  keys=Seen(known-{key(p)} if skip else known);st,w=search(fixed,set(pre),191,50000,known=keys,allowed=fixed|free)
  if w:assert valid(w) and key(w) not in set(keys)
  output.append([skip,st,keys.blocked,w])
 assert output[0][3] and key(output[0][3])==key(p);(r/'blocked-control.json').write_text(json.dumps(output,separators=(',',':')))
def main():
 refs=json.loads((r/'reference.json').read_text());ctrl(refs);known=Seen(key(p) for p in refs);src={}
 for f in ('q9_all190_20261119.csv','q9_beam190_20261119.csv','q9_nonlocal189_seeds19.csv'):
  for z in csv.DictReader(open('/tmp/'+f)):
   p=list(map(int,z['vertices'].split()));src.setdefault(key(p),p)
 priv={key(p) for p,s in json.loads((r/'seeds.json').read_text())};data=list(src.values());other=[i for i,p in enumerate(data) if key(p) not in priv];rng=Random(559100);start=monotonic();c=Counter()
 with (r/'blocked.jsonl').open('w',1) as out:
  for t in range(12500):
   i=rng.choice(other) if t%2 else rng.randrange(len(data));p=data[i];cols,syn=code(rng);R=set(rng.sample(range(16),rng.choice([5,6,7,8,9])))
   used=set(p);force=set()
   if t%3:
    end=rng.choice([p[0],p[-1]]);options=[end^(1<<j) for j in range(9) if end^(1<<j) not in used];y=min(options,key=lambda v:len([x for x in used if (x^v).bit_count()==1])+rng.random()*2);force={end,y}
    R.update(syn[x] for x in used if x!=end and (x^y).bit_count()==1)
   free={x for x in range(512) if syn[x] in R};F=(used-free)|force;size=known.blocked
   st,w=search(F,used,191,4200,known=known,allowed=free|F);c[st]+=1
   if w:
    assert valid(w) and len(w)==192 and key(w) not in set(known)
    ex=extend(w);assert all(valid(a) for a in ex);(r/'blocked-positive.json').write_text(json.dumps([w,ex]))
   print(json.dumps([i,cols,sorted(R),sorted(force),st,known.blocked-size,w],separators=(',',':')),file=out)
   if w or monotonic()-start>60:break
 print('sources',len(data),'without_private_span',len(other),'rejected_known_models',known.blocked,'outcomes',dict(c))
if __name__=='__main__':main()

