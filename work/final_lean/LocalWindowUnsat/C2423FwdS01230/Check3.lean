import LocalWindowUnsat.C2423FwdS01230.Data12

/-! Kernel checks of segments 9-12 of `2423_fwd_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423FwdS01230
open Snake9.Lrat

theorem ok9 : andB (check start9 proof9) (cpOk (replay start9 proof9) cp10) = true := by
  decide +kernel

theorem ok10 : check start10 proof10 = true := by
  decide +kernel

theorem ok11 : check start11 proof11 = true := by
  decide +kernel

theorem ok12 : andB (check start12 proof12) (cpOk (replay start12 proof12) cp13) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423FwdS01230
