from run import *
def constraints():
 for line in (D/'near.txt').read_text().splitlines():
  r,score,n,*q=map(int,line.split());assert len(q)==n
  chords=[[a,b] for i,a in enumerate(q) for b in q[i+2:] if (a^b).bit_count()<2]
  assert chords and len(set(q))==len(q) and len(chords)==score
  base={v//32 for c in chords for v in c};left=sorted(set(range(16))-base)
  for extras in (0,1,2):
   for tup in itertools.combinations(left,extras):yield r,q,base|set(tup)
if __name__=='__main__':
 for i,(r,q,f) in enumerate(constraints()):
  fi={v for v in q if v//32 not in f};al=fi|{v for v in range(512) if v//32 in f}
  st,p=search(fi,set(q),192,5000,allowed=al,at_least=True)
  print(json.dumps([i,r,sorted(f),st,p],separators=(',',':')),flush=True)
  if p:break
