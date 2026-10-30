"""Compare exact fixed-potential selections before and after proved pruning."""
from pathlib import Path
import collections,gzip,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(gzip.decompress(p.read_bytes()))
old=read(ROOT/'milestones/69-count-certificate-selection/data/selection-14387.json.gz')
new=read(HERE/'data/old-selection.json.gz');fresh=read(HERE/'data/selection.json.gz')
assert old['source_potential_sha256']==new['potential_sha256']
assert all(old[k]==new[k] for k in ['potential_numerator','potential_denominator'])
oldids=set(old['selected_ids']);newids=set(new['selected_ids'])
assert newids<=oldids
oldclauses={tuple(c['keys']) for c in old['clauses']};newclauses={tuple(c['keys']) for c in new['clauses']}
assert newclauses<=oldclauses
widths=lambda data:dict(sorted(collections.Counter(len(cs) for w,cs in data['keys']).items()))
out=dict(status='PASS',previous_selected=len(oldids),retained_selected=len(newids),removed_obligations=len(oldids-newids),reduction_percent=100*len(oldids-newids)/len(oldids),previous_widths=widths(old),retained_widths=widths(new),recomputed_potential_widths=widths(fresh),new_clauses_subset_old=True,new_selection_subset_old=True,removed_ids=sorted(oldids-newids),scope='A smaller sufficient premise set after integrating existing proofs. Removed keys have not individually been proved here. This is not a globally minimal proof programme.')
(HERE/'data/comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='removed_ids'})
