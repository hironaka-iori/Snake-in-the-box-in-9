import LocalWindowUnsat.C2423FwdS01230.Data72

/-! Kernel checks of segments 69-72 of `2423_fwd_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423FwdS01230
open Snake9.Lrat

theorem ok69 : andB (check start69 proof69) (cpOk (replay start69 proof69) cp70) = true := by
  decide +kernel

theorem ok70 : check start70 proof70 = true := by
  decide +kernel

theorem ok71 : check start71 proof71 = true := by
  decide +kernel

theorem ok72 : andB (check start72 proof72) (cpOk (replay start72 proof72) cp73) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423FwdS01230
