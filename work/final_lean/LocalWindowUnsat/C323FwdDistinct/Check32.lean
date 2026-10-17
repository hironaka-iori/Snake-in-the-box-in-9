import LocalWindowUnsat.C323FwdDistinct.Data128

/-! Kernel checks of segments 125-128 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok125 : check start125 proof125 = true := by
  decide +kernel

theorem ok126 : andB (check start126 proof126) (cpOk (replay start126 proof126) cp127) = true := by
  decide +kernel

theorem ok127 : check start127 proof127 = true := by
  decide +kernel

theorem ok128 : check start128 proof128 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
