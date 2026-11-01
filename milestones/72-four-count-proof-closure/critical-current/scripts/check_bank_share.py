"""Check complete bank snakes and compute exact five-centre shares by shape."""
from pathlib import Path
from itertools import combinations
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
source=ROOT/'work/bank9.json';bank=json.loads(source.read_text());pairs=list(combinations(range(9),2))
def canon(w):
 d={};return tuple(d.setdefault(x,len(d)) for x in w)
mins={};occurrences=0
for b,row in enumerate(bank):
 path=row['vertex_sequence'];S=set(path)
 assert len(path)==len(S)==192
 assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path) if i<j)
 degree=[sum((q^(1<<a)) in S for a in range(9)) for q in range(512)]
 empty=[sum(not(S&{q,q^(1<<a),q^(1<<c),q^(1<<a)^(1<<c)}) for a,c in pairs) for q in range(512)]
 share=[sum(12*empty[v^(1<<a)]//degree[v^(1<<a)] for a in range(9)) for v in path]
 ds=[(x^y).bit_length()-1 for x,y in zip(path,path[1:])]
 for r in range(len(ds)-5):
  word=ds[r:r+6];shape=min(canon(word),canon(word[::-1]));value=sum(share[r+1:r+6]);occurrences+=1
  if shape not in mins or value<mins[shape]['share']:
   mins[shape]=dict(directions=list(shape),share=value,bank_index=b,start=r,centre_shares=share[r+1:r+6])
out=dict(status='PASS_BANK_ENUMERATION',bank_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),paths=len(bank),windows=occurrences,minimum=min(x['share'] for x in mins.values()),by_shape=[mins[s] for s in sorted(mins)],scope='Exact census on 131 checked complete 191-edge snakes. These are examples, not a universal lower bound.')
(HERE/'data/bank-share.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
