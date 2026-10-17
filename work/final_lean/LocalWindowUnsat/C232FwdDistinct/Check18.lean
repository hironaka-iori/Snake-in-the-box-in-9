import LocalWindowUnsat.C232FwdDistinct.Data71

/-! Kernel checks of segments 69-71 of `232_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C232FwdDistinct
open Snake9.Lrat

theorem ok69 : andB (check start69 proof69) (cpOk (replay start69 proof69) cp70) = true := by
  decide +kernel

theorem ok70 : check start70 proof70 = true := by
  decide +kernel

theorem ok71 : andB (check start71 proof71) (hasEmpty (replay start71 proof71) 1483) = true := by
  decide +kernel

end Snake9.LocalWindow.C232FwdDistinct
