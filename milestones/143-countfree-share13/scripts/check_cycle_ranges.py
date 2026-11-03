"""Construct potentials on the saved nine-cycle, without assuming a full graph potential."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
H=Path(__file__).resolve().parents[1]
p=H/'data/range-analysis.json';j=json.loads(p.read_text());rows=[]
for r in j['rows']:
 mean=F(r['mean']);a=[F(0)]
 for w in r['weights']:a.append(a[-1]+w-mean)
 assert a[-1]==0
 low=min(a);pot=[x-low for x in a[:-1]]
 assert all(mean+pot[(i+1)%9]==w+pot[i] for i,w in enumerate(r['weights']))
 ran=max(pot)-min(pot);assert ran==F(r['minimum_cycle_only_range_at_mean'])
 i=r['max_deficit_walk_start'];k=r['walk_length']
 assert pot[i]-pot[(i+k)%9]==ran==k*mean-r['walk_weight']
 rows.append(dict(floor=r['floor'],potentials=list(map(str,pot)),range=str(ran),all_nine_inequalities_equalities=True,recorded_walk_attains_range=True))
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
out=dict(status='PASS_CYCLE_ONLY_RANGE_ATTAINMENT',rows=rows,source_files_sha256={str(p):sha(p),str(Path(__file__)):sha(Path(__file__))},scope='At the mean of this nine-cycle, every potential inequality on the cycle is equality. The constructed potential attains the range forced by the saved subwalk. No extension to the full graph is asserted.')
(H/'data/cycle-range-attainment.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'])
