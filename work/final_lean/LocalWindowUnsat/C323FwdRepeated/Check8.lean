import LocalWindowUnsat.C323FwdRepeated.Data32

/-! Kernel checks of segments 29-32 of `323_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdRepeated
open Snake9.Lrat

theorem ok29 : check start29 proof29 = true := by
  decide +kernel

theorem ok30 : andB (check start30 proof30) (cpOk (replay start30 proof30) cp31) = true := by
  decide +kernel

theorem ok31 : check start31 proof31 = true := by
  decide +kernel

theorem ok32 : check start32 proof32 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdRepeated
