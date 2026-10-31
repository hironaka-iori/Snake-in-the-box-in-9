"""Independent full-cube snake validator; no CNF or project helper imports."""
from collections import Counter

def validate(selected,window=(),n=9):
 seq=list(selected);S=set(seq)
 if len(seq)!=len(S) or len(S)<2 or any(not isinstance(v,int) or not 0<=v<1<<n for v in S):raise ValueError('need distinct valid vertices of a nontrivial snake')
 adj={x:[y for y in S if (x^y).bit_count()==1] for x in S}
 ends=[v for v in S if len(adj[v])==1]
 if len(ends)!=2 or any(len(adj[v]) not in (1,2) for v in S):raise ValueError('global degrees/endpoints fail')
 ordered=[];previous=None;current=min(ends)
 while current is not None:
  if current in ordered:raise ValueError('repeated traversal vertex')
  ordered.append(current);following=[v for v in adj[current] if v!=previous]
  if len(following)>1:raise ValueError('branch')
  previous,current=current,(following[0] if following else None)
 if set(ordered)!=S:raise ValueError('disconnected cycle component')
 w=list(window)
 if w and not any(ordered[i:i+len(w)]==w or ordered[i:i+len(w)]==w[::-1] for i in range(len(ordered)-len(w)+1)):raise ValueError('window not consecutive')
 return {'vertices':len(S),'edges':len(S)-1,'ordered_vertices':ordered,'all_pair_adjacency_checked':True}

def self_test():
 assert validate([0,1,3],[0,1,3])['edges']==2
 rejected=0
 for bad in ([0],[0,1,3,7,6,4],[0,1,510,511],[0,0,1]):
  try:validate(bad)
  except ValueError:rejected+=1
 assert rejected==4
 return {'positive':1,'negative':rejected}
if __name__=='__main__':print(self_test())
