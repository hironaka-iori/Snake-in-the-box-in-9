from search import *
def run():
 data=json.loads((r/'seeds.json').read_text());refs={key(p) for p in json.loads((r/'reference.json').read_text())};c=Counter()
 with (r/'retry.jsonl').open('w',1) as out:
  for name in sys.argv[1:]:
   for j,l in enumerate((r/(name+'.jsonl')).open()):
    idx,cols,R,span,force,goal,st,_=json.loads(l)
    if st!='UNKNOWN':continue
    syn=[0]*512
    for n in range(1,512):syn[n]=syn[n&(n-1)]^cols[(n&-n).bit_length()-1]
    p=data[idx][0];t,L=span;free={x for x in range(512) if syn[x] in R};F=(set(p)-free)|set(p[t:t+L])|set(force)
    st,w=search(F,set(p),goal,110000,allowed=F|free,at_least=True);c[st]+=1
    if w:
     assert valid(w) and (len(w)>192 or key(w) not in refs);ext=extend(w);assert all(valid(q) for q in ext);(r/'retry-positive.json').write_text(json.dumps([w,ext]))
    print(json.dumps([name,j,idx,goal,st,w]),file=out)
    if w:break
 print(dict(c))
if __name__=='__main__':run()

