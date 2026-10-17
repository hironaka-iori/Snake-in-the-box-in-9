import LocalWindowUnsat.C323FwdDistinct.Data52

/-! Kernel checks of segments 49-52 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok49 : check start49 proof49 = true := by
  decide +kernel

theorem ok50 : check start50 proof50 = true := by
  decide +kernel

theorem ok51 : andB (check start51 proof51) (cpOk (replay start51 proof51) cp52) = true := by
  decide +kernel

theorem ok52 : check start52 proof52 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
