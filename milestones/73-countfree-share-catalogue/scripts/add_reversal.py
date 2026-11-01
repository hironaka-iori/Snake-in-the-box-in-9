"""Generate a direct reversal wrapper for each named-coordinate share theorem."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parents[1]
OUT=HERE/'cases'/f'case{int(sys.argv[1])}'
case=json.loads((OUT/'data/case.json').read_text())
ds=case['selected']['directions'];names=list('abcdef')[:max(ds)+1]
u='['+','.join(names)+']';word='['+','.join(names[d] for d in reversed(ds))+']'
short=case['prefix'];namespace=case['namespace'];lower=case['selected']['required_share']
source=f'''import {short}.Geometry
namespace Snake9.LocalWindow.{namespace}
set_option maxHeartbeats 1000000
theorem share_bound_rev {{m : Nat}} (p : Snake m) (r {' '.join(names)} : Nat)
    (hn : {u}.Nodup) (h9 : ∀ x ∈ {u}, x < 9)
    (hr : r + 6 ≤ m)
    (hd : ∀ j, j < 6 → dir p (r+j) = ({word} : List Nat).getD j 0) :
    {lower} ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have result := share_bound (revSnake p) (m-r-6) {' '.join(names)} hn h9
    (by omega)
    (by
      intro j hj
      rw [dir_rev p (by omega), show m - (m-r-6+j) - 1 = r + (5-j) by omega,
        hd (5-j) (by omega)]
      interval_cases j <;> rfl)
  have hs := coreShare_window_rev 12 p r 5 (by omega)
  rw [show m-r-5-1 = m-r-6 by omega] at hs
  rw [hs] at result
  exact result
#print axioms share_bound_rev
end Snake9.LocalWindow.{namespace}
'''
(OUT/f'lean/{short}/Reversal.lean').write_text(source,encoding='utf-8',newline='\n')
print('Generated reversal wrapper',case['case_number'])
