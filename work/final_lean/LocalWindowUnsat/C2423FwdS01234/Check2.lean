import LocalWindowUnsat.C2423FwdS01234.Data8

/-! Kernel checks of segments 5-8 of `2423_fwd_s01234` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423FwdS01234
open Snake9.Lrat

theorem ok5 : check start5 proof5 = true := by
  decide +kernel

theorem ok6 : andB (check start6 proof6) (cpOk (replay start6 proof6) cp7) = true := by
  decide +kernel

theorem ok7 : check start7 proof7 = true := by
  decide +kernel

theorem ok8 : andB (check start8 proof8) (hasEmpty (replay start8 proof8) 1019) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423FwdS01234
