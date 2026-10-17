import LocalWindowUnsat.C2423FwdS01230.Data28

/-! Kernel checks of segments 25-28 of `2423_fwd_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423FwdS01230
open Snake9.Lrat

theorem ok25 : check start25 proof25 = true := by
  decide +kernel

theorem ok26 : check start26 proof26 = true := by
  decide +kernel

theorem ok27 : andB (check start27 proof27) (cpOk (replay start27 proof27) cp28) = true := by
  decide +kernel

theorem ok28 : check start28 proof28 = true := by
  decide +kernel

end Snake9.LocalWindow.C2423FwdS01230
