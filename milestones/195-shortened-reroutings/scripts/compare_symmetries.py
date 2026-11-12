"""Look for the same involution type in the Q9 four-crossing bank."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];source=H/'data/forest-profiles.json';raw=source.read_bytes();data=json.loads(raw)
matches=[];candidates=[]
for index,row in enumerate(data['bank_forests']):
 p,q=row['paths']
 if len(p)!=len(q):continue
 a=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
 for reverse in [False,True]:
  r=q[::-1] if reverse else q;b=[(u^v).bit_length()-1 for u,v in zip(r,r[1:])];mp=dict(zip(a,b))
  if len(mp)!=8 or len(set(mp.values()))!=8 or any(mp[x]!=y for x,y in zip(a,b)):continue
  f=lambda x:sum(((x>>i)&1)<<mp[i] for i in range(8))
  shift=f(p[0])^r[0];t=lambda x:f(x)^shift
  if any(t(x)!=y for x,y in zip(p,r)):continue
  moved=[k for k in range(8) if mp[k]!=k];flipped=[k for k in range(8) if mp[k]==k and (shift>>k)&1]
  record=dict(forest=index,edges=len(p)-1,reversed=reverse,permutation=[mp[i] for i in range(8)],translation=shift,
    involution=all(t(t(v))==v for v in range(256)),moved_coordinates=moved,flipped_fixed_coordinates=flipped)
  candidates.append(record)
  if len(moved)!=2 or len(flipped)!=3 or not record['involution']:continue
  remainder=[k for k in range(8) if k not in moved+flipped];mapping={}
  for old,new in zip(moved+flipped+remainder,[2,5,0,3,6,1,4,7]):mapping[old]=new
  h0=lambda x:sum(((x>>i)&1)<<mapping[i] for i in range(8))
  correction=4 if (h0(shift)>>2)&1 else 0
  h=lambda x:h0(x)^correction
  g=lambda v:(v^(((v>>2)^(v>>5))&1)*36)^73
  assert all(h(t(v))==g(h(v)) for v in range(256))
  path=[h(v) for v in p];partner=[g(v) for v in path];quotient=[min(v,g(v)) for v in path]
  assert len(set(quotient))==len(path)
  record.update(conjugating_permutation=[mapping[i] for i in range(8)],conjugating_translation=correction,paths=[path,partner],quotient_path=quotient)
  matches.append(record)
out=dict(status='COMPLETE',source_sha256=hashlib.sha256(raw).hexdigest(),candidates=candidates,matches=matches,
    scope='Labelled isometries determined by corresponding transitions, allowing reversal; all eight directions must occur. No classification of other pair symmetries.')
target=H/'data/symmetry-comparison.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(candidates=len(candidates),matches=len(matches),lengths=dict(collections.Counter(r['edges'] for r in matches)))))
