"""Reproduce the finite distance-two sphere intersection table."""
from pathlib import Path
import collections,json
H=Path(__file__).resolve().parents[1]
a=json.loads((H/'data/sphere-intersection-check.json').read_text())
twos=[v for v in range(512) if v.bit_count()==2]
rows=[]
for delta in range(1,512):
    count=sum((v^delta).bit_count()==2 for v in twos)
    expected=14 if delta.bit_count()==2 else 6 if delta.bit_count()==4 else 0
    assert count==expected
    rows.append([delta,delta.bit_count(),count])
assert rows==a['rows'] and max(x[2] for x in rows)==a['maximum_intersection']==14
assert {str(k):v for k,v in collections.Counter(x[2] for x in rows).items()}==a['counts_by_intersection']
print('PASS_FINITE_TRANSLATED_SPHERE_COUNTS',len(rows),'differences; maximum14')
