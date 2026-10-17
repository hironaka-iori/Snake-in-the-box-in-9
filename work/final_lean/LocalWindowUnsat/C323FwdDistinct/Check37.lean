import LocalWindowUnsat.C323FwdDistinct.Data148

/-! Kernel checks of segments 145-148 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok145 : check start145 proof145 = true := by
  decide +kernel

theorem ok146 : check start146 proof146 = true := by
  decide +kernel

theorem ok147 : andB (check start147 proof147) (cpOk (replay start147 proof147) cp148) = true := by
  decide +kernel

theorem ok148 : check start148 proof148 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
