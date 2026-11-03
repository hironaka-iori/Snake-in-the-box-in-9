"""Count integer count-vectors only, to size the proposed exhaustive split."""
from pathlib import Path
from math import comb
import hashlib,json
H=Path(__file__).resolve().parents[1]
lower=[1,2,1,3,1,1]
def vectors(i,budget,prefix=()):
 if i==6:
  yield prefix
  return
 for x in range(lower[i],min(21,budget-sum(lower[i+1:]))+1):
  yield from vectors(i+1,budget-x,prefix+(x,))
total=pair=both=equal=larger=0
for row in vectors(0,22):
 total+=1
 assert len(row)==6 and sum(row)<=22 and all(lo<=x<=21 for lo,x in zip(lower,row))
 if row[1]+row[3]<8:continue
 pair+=1
 if row[0]<=2 and row[3]<=3:continue
 both+=1
 if row[3]==3:
  equal+=1
  assert row[0]>=3 and row[1]>=5 and row[2]+row[4]+row[5]<=11
 else:
  larger+=1
  assert row[3]>=4
assert total==comb(19,6)==27132
assert equal==comb(13,5)==1287
assert larger==comb(18,6)-comb(16,4)-2*comb(15,4)==14014
assert pair==larger+comb(15,5)==17017
assert both==equal+larger==15301
out=dict(status='PASS_EXHAUSTIVE_INTEGER_VECTOR_SPLIT_ONLY',total_cap=22,
 necessary_intervals=[(x,21) for x in lower],before_pair=total,after_pair=pair,
 after_pair_and_first_fourth_exclusion=both,fourth_equals_three=equal,fourth_at_least_four=larger,
 first_branch_other_three_cap=11,all_first_branch_vectors_obey_deduced_bounds=True,
 independent_binomial_counts_match=True,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 scope='Integer count-vectors satisfying only these listed necessary inequalities. Most need not be geometrically realizable. This enumeration gives no snake exclusion and is not a Lean proof of the proposed split assembly.')
p=H/'data/next-split-counts.json';assert not p.exists()
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
