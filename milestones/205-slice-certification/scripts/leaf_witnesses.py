"""Extract explicit global cube isometries for the finite model's saved leaves."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
seed=json.loads((H/'data/lower-dimensional-input.json').read_bytes())['8']['vertices']
def spread(x,coordinates):return sum(((x>>i)&1)<<c for i,c in enumerate(coordinates))
def permute(x,p):return sum(((x>>i)&1)<<c for i,c in enumerate(p))
records=[]
for k in range(254):
 d=json.loads((H/'data'/f'partition-{k}.json').read_bytes())
 c=json.loads((H/'data'/f'cover-{k}.json').read_bytes());pos={z:i for i,z in enumerate(d['occupied'])}
 for leafno,values in enumerate(c['leaves']):
  image=[spread(z,d['base_coordinates'])+spread(d['domains'][pos[z]][values[pos[z]]][u],d['block_coordinates']) for z,u in d['vertices']]
  witness=None
  for reverse in [False,True]:
   original=seed[::-1] if reverse else seed
   p={};good=True
   for a,b,x,y in zip(original,original[1:],image,image[1:]):
    da=a^b;db=x^y
    if da.bit_count()!=1 or db.bit_count()!=1:good=False;break
    i=da.bit_length()-1;j=db.bit_length()-1
    if i in p and p[i]!=j:good=False;break
    p[i]=j
   if not good or len(set(p.values()))!=len(p):continue
   for i,j in zip(sorted(set(range(8))-set(p)),sorted(set(range(8))-set(p.values()))):p[i]=j
   permutation=[p[i] for i in range(8)];offset=image[0]^permute(original[0],permutation)
   if all(y==(permute(x,permutation)^offset) for x,y in zip(original,image)):
    witness=dict(reverse=reverse,permutation=permutation,offset=offset);break
  assert witness is not None,(k,leafno)
  records.append(dict(partition=k,leaf=leafno,assignment=values,image=image,**witness))
out=dict(records=records,partitions=254,leaves=len(records),scope='Native explicit witnesses, each verified at all 99 indexed vertices. These are not Lean certificates.',source_sha256=hashlib.sha256((H/'data/lower-dimensional-input.json').read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(H/'data/leaf-witnesses.json').write_text(json.dumps(out,indent=2)+'\n');print('EXPLICIT_NATIVE_WITNESSES',len(records))
