import LocalWindowUnsat.C323FwdDistinct.Data160

/-! Kernel checks of segments 157-160 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok157 : check start157 proof157 = true := by
  decide +kernel

theorem ok158 : check start158 proof158 = true := by
  decide +kernel

theorem ok159 : andB (check start159 proof159) (cpOk (replay start159 proof159) cp160) = true := by
  decide +kernel

theorem ok160 : check start160 proof160 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
