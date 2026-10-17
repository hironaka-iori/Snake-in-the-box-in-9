import LocalWindowUnsat.C2423FwdS01230.Data40

/-! Kernel checks of segments 37-40 of `2423_fwd_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423FwdS01230
open Snake9.Lrat

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : andB (check start39 proof39) (cpOk (replay start39 proof39) cp40) = true := by
  decide +kernel

theorem ok40 : check start40 proof40 = true := by
  decide +kernel

end Snake9.LocalWindow.C2423FwdS01230
