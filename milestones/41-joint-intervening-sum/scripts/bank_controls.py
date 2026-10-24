"""Independent full-path census; occurrence frequencies are observations, not coverage."""
from pathlib import Path
from collections import Counter
import hashlib,itertools,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
bankfile=ROOT/'work/bank9.json';bank=json.loads(bankfile.read_text());matches=[]
def canonical(ds):
 names={};return [names.setdefault(d,len(names)) for d in ds]
for k,row in enumerate(bank):
 vs=row['vertex_sequence'];S=set(vs)
 assert len(vs)==len(S) and all(0<=v<512 for v in S)
 assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
 alpha=[sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in itertools.combinations(range(9),2)) for v in vs]
 ds=[(u^v).bit_length()-1 for u,v in zip(vs,vs[1:])]
 for r in range(len(ds)-7):
  for rev in [False,True]:
   d=ds[r:r+8];aa=alpha[r+1:r+8]
   if rev:d=d[::-1];aa=aa[::-1]
   if canonical(d)!=[0,1,2,3,4,2,0,3]:continue
   qualifies=aa[0]<=3 and aa[-1]<=3
   if qualifies:assert aa[2]+aa[5]>=12
   matches.append(dict(bank_index=k,start=r,reversed=rev,counts=aa,qualifies=qualifies))
out=dict(verified_paths=len(bank),bank_sha256=hashlib.sha256(bankfile.read_bytes()).hexdigest(),occurrences=matches,qualifying_occurrences=sum(r['qualifies'] for r in matches),scope='Observed occurrences in the published bank; not a classification of all snakes or a frequency theorem.')
(HERE/'data/bank-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(len(bank),'paths;',len(matches),'pattern occurrences;',out['qualifying_occurrences'],'qualifying')
